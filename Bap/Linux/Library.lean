import Bap.Linux.Machine
import Bap.Image.Elf

/-! Shared libraries loaded into a machine from outside it, as `dlopen`, `dlsym` and `dlclose` would be from inside: without a libc or a
dynamic linker in the guest, for what wants to call a library in a guest, such as the native code of an Android application. What a
program loads for itself is another thing, and goes as it does on Linux, by its own `PT_INTERP`.

Everything is bound when it is loaded. A relocation that this doesn't know is an error and not something to leave undone, and so is one
of thread-local storage: what it comes to is an offset from a thread pointer, in the layout of a libc that isn't here. -/

namespace Bap.Linux

open Bap.Emu

/-- How to call a function of a target: arguments in registers, where a return address goes, where the result is. -/
private structure CallConvention where
  arguments : List String
  link : Option String
  result : String
  /-- What goes in a register for a function to find itself by. -/
  self : Option String := none

private def conventionOf : Architecture → CallConvention
  | .x86_64 => { arguments := ["RDI", "RSI", "RDX", "RCX", "R8", "R9"], link := none, result := "RAX" }
  | .i686 => { arguments := [], link := none, result := "EAX" }
  | .aarch64 => { arguments := (List.range 8).map (s!"X{·}"), link := some "X30", result := "X0" }
  | .arm => { arguments := ["R0", "R1", "R2", "R3"], link := some "LR", result := "R0" }
  | .riscv64 | .riscv32 => { arguments := (List.range 8).map (s!"X{10 + ·}"), link := some "X1", result := "X10" }
  | .mips 32 _ _ => { arguments := ["R4", "R5", "R6", "R7"], link := some "R31", result := "R2", self := some "R25" }
  | .mips _ _ _ => { arguments := (List.range 8).map (s!"R{4 + ·}"), link := some "R31", result := "R2", self := some "R25" }
  | .powerpc 32 _ => { arguments := (List.range 8).map (s!"R{3 + ·}"), link := some "LR", result := "R3" }
  | .powerpc _ _ => { arguments := (List.range 8).map (s!"R{3 + ·}"), link := some "LR", result := "R3", self := some "R12" }

/-- Where a function called from outside returns to, which is a page that nothing runs. -/
private def callReturnPage (machine : Machine) : Nat := machine.signals.returnPage + 4096

private def numberBytes (big : Bool) (size value : Nat) : ByteArray :=
  let little := (List.range size).map fun index => (value >>> (8 * index)).toUInt8
  ByteArray.mk (if big then little.reverse else little).toArray

/-- Calls a function of the guest with these arguments, on the stack of the thread that runs and in it, and says what it gives back.
Nothing else runs meanwhile. What it did to memory stays, and its registers go back. What doesn't return, by `fuel` instructions or
because it faults or stops, is an error. It can't be done in the middle of an instruction. -/
def Machine.call (machine : Machine) (address : Nat) (arguments : List Nat := []) (fuel : Nat := 100000000) : IO Nat := do
  let emu := machine.emu
  if ← emu.serving.get then
    throw <| IO.userError "a function can't be called in the middle of an instruction: stop the thread, and call it once the run returns"
  let architecture := machine.architecture
  let convention := conventionOf architecture
  let width := architecture.bits
  let word := width / 8
  let big := architecture.big
  let register (name : String) : Bap.Var := ⟨name, .imm width, 0, false⟩
  let set (name : String) (value : Nat) : IO Unit := setReg emu (register name) (.bits (BitVec.ofNat width value))
  let stackRegister := match architecture with
    | .x86_64 => "RSP"
    | .i686 => "ESP"
    | .aarch64 | .arm => "SP"
    | .riscv64 | .riscv32 => "X2"
    | .mips .. => "R29"
    | .powerpc .. => "R1"
  if !(architecture matches .i686) && arguments.length > convention.arguments.length then
    throw <| IO.userError s!"a call of {arguments.length} arguments, and this has {convention.arguments.length} registers for them"
  -- All that goes back.
  let memoryVar := emu.config.memory
  let saved := (← emu.state.get).env.filter fun binding => binding.1 != memoryVar
  let savedPc ← emu.pc.get
  let savedPending ← emu.pendingRef.get
  let savedSkip ← emu.skipCode.get
  let savedStopped ← emu.stopped.get
  let savedFault ← emu.lastFault.get
  let returnTo := callReturnPage machine
  if (lookupRegion (← emu.regions.get) returnTo).isNone then
    Bap.Emu.map emu ⟨returnTo, ByteArray.mk (Array.replicate 4096 0), ⟨true, false, true⟩⟩
  let restore : IO Unit := do
    let current ← emu.state.get
    emu.state.set { env := saved ++ current.env.filter fun binding => binding.1 == memoryVar }
    emu.pc.set savedPc
    emu.pendingRef.set savedPending
    emu.skipCode.set savedSkip
    emu.stopped.set savedStopped
    emu.lastFault.set savedFault
  let breakpoint ← addBreakpoint emu returnTo
  try
    let readStack ← match Bil.lookup (← emu.state.get).env (register stackRegister) with
      | .ok (.bits value) => pure value.toNat
      | _ => throw <| IO.userError "the stack of this thread isn't there"
    -- Below what a function may use without saying so, and as a call would have it.
    let below := readStack - 512
    let entrySp ← match architecture with
      | .x86_64 =>
        let sp := below / 16 * 16 - 8
        Bap.Emu.write emu sp (numberBytes false 8 returnTo)
        pure sp
      | .i686 =>
        let sp := (below - arguments.length * 4) / 16 * 16 - 4
        Bap.Emu.write emu sp (numberBytes false 4 returnTo)
        for (argument, index) in arguments.zipIdx do
          Bap.Emu.write emu (sp + 4 + index * 4) (numberBytes false 4 argument)
        pure sp
      | .mips .. => pure (below / 16 * 16 - 32)
      | .powerpc _ _ =>
        let sp := below / 16 * 16 - 128
        Bap.Emu.write emu sp (numberBytes big word 0)
        pure sp
      | _ => pure (below / 16 * 16)
    set stackRegister entrySp
    if !(architecture matches .i686) then
      for (argument, name) in arguments.zip convention.arguments do
        set name argument
    if let some link := convention.link then set link returnTo
    if let some self := convention.self then set self address
    if architecture matches .arm then
      setReg emu ⟨"ISET", .imm 1, 0, false⟩ (.bits (BitVec.ofNat 1 (address % 2)))
      setPc emu (address - address % 2)
    else setPc emu address
    emu.stopped.set false
    let _ ← Bap.Emu.run emu fuel
    let reached ← emu.pc.get
    if reached != returnTo then
      throw <| IO.userError s!"a call of {address} didn't return: it is at {reached}"
    match Bil.lookup (← emu.state.get).env (register convention.result) with
    | .ok (.bits value) =>
      removeHook emu breakpoint
      restore
      pure value.toNat
    | _ => throw <| IO.userError "a call has no result"
  catch error =>
    removeHook emu breakpoint
    restore
    throw error

/-- What a relocation of a target asks for. -/
private inductive RelocationKind where
  | none
  | relative
  | indirect
  /-- A symbol, and what is added. -/
  | absolute
  /-- A symbol, as a table of them has it. -/
  | slot
  | threadLocal
  | unknown

private def relocationKind (machine typ : Nat) (is64 : Bool) : RelocationKind :=
  let types (none : List Nat) (relative indirect : List Nat) (absolute slot threadLocal : List Nat) : RelocationKind :=
    if none.contains typ then .none
    else if relative.contains typ then .relative
    else if indirect.contains typ then .indirect
    else if absolute.contains typ then .absolute
    else if slot.contains typ then .slot
    else if threadLocal.contains typ then .threadLocal
    else .unknown
  match machine with
  | 62 => types [0] [8] [37] [1] [6, 7] [16, 17, 18, 36]
  | 3 => types [0] [8] [42] [1] [6, 7] [14, 15, 35, 36, 37, 38, 39]
  | 183 => types [0] [1027] [1032] [257] [1025, 1026] [1028, 1029, 1030, 1031]
  | 40 => types [0] [23] [160] [2] [21, 22] [17, 18, 19, 90, 91, 92, 93]
  | 243 => types [0] [3] [58] [if is64 then 2 else 1] [5] [6, 7, 8, 9, 10, 11, 12]
  | 20 => types [0] [22] [248] [1] [20, 21] [67, 68, 69, 70, 71, 72, 73, 74, 75, 78]
  | 21 => types [0] [22] [248] [38] [20, 21] [67, 68, 73, 78]
  -- REL32 has a symbol or doesn't, and with MIPS64 what is stacked on it is only how wide it is.
  | 8 => match typ % 256 with
    | 0 => .none
    | 3 => .absolute
    | 38 | 39 | 40 | 41 | 47 | 48 => .threadLocal
    | _ => .unknown
  | _ => .unknown

private def sameMachine (architecture : Architecture) (program : Elf.Program) : Bool :=
  let (number, bits, big, _) := architecture.elf
  program.machine == number && program.bits == bits && program.big == big

private def baseName (path : String) : String := (path.splitOn "/").getLast?.getD path

private def spaceHas (space : Nat) (table : Std.HashMap Nat (List LoadedLibrary)) : List LoadedLibrary :=
  table.getD space []

/-- What it needs, found in the machine: by a path, by what a library says to look in, by what is asked, and where libraries are. -/
private def findLibrary (machine : Machine) (name origin : String) (runPaths search : List String) : IO (Option String) := do
  let kernel ← machine.kernel.get
  let exists_ (path : String) : Bool := match Kernel.resolve kernel "/" path with
    | .ok (_, some _) => true
    | _ => false
  if name.contains '/' then return if exists_ name then some name else none
  let expanded := runPaths.map fun path => (path.replace "$ORIGIN" origin).replace "${ORIGIN}" origin
  let places := expanded ++ search ++ ["/lib", "/usr/lib", "/lib64", "/usr/lib64"]
  pure ((places.map (· ++ "/" ++ name)).find? exists_)

/-- What makes up a load, to undo it as a whole. -/
private structure Loading where
  /-- What it found to be new, by path. -/
  mapped : List LoadedLibrary := []
  /-- What to run, in order: the first that was loaded and all that it needed last. -/
  initializers : List Nat := []

/-- Maps a library, with everything writable until it has been relocated. -/
private def mapLibrary (machine : Machine) (path : String) (data : ByteArray) (program : Elf.Program) : IO (Nat × Nat × Nat) := do
  let emu := machine.emu
  if program.segments.isEmpty then throw <| IO.userError s!"{path} has nothing to load"
  let lowest := program.segments.foldl (fun lowest segment => min lowest segment.address) (2 ^ 64)
  let highest := program.segments.foldl (fun highest segment => max highest (segment.address + segment.memorySize)) 0
  let first := lowest / 4096 * 4096
  let span := (highest + 4095) / 4096 * 4096 - first
  let start ← placeMapping emu 0 false (zeroBytes span) 3
  let base := start - first
  for segment in program.segments do
    Bap.Emu.write emu (base + segment.address) (data.extract segment.offset (segment.offset + segment.fileSize))
  pure (base, start, span)

/-- Gives a library its real protections, once what is in it has been written. -/
private def protectLibrary (machine : Machine) (image : Image.Image) (base : Nat) (program : Elf.Program) : IO Unit := do
  let emu := machine.emu
  let up (value : Nat) : Nat := (value + 4095) / 4096 * 4096
  let down (value : Nat) : Nat := value / 4096 * 4096
  let lowest := program.segments.foldl (fun lowest segment => min lowest segment.address) (2 ^ 64)
  let highest := program.segments.foldl (fun highest segment => max highest (segment.address + segment.memorySize)) 0
  -- What no segment has is nothing that anything should reach.
  protect emu (base + down lowest) (up highest - down lowest) ⟨false, false, false⟩
  for segment in program.segments do
    let (start, stop) := (down segment.address, up (segment.address + segment.memorySize))
    protect emu (base + start) (stop - start) ⟨segment.flags &&& 4 != 0, segment.flags &&& 2 != 0, segment.flags &&& 1 != 0⟩
  -- What is only written to by relocating it. As Linux has it, what is left over at its end stays writable.
  if let some relro := Image.Elf.programHeaderOf image 0x6474e552 then
    let start := down relro.addr
    let stop := down (relro.addr + relro.memorySize)
    if start < stop then protect emu (base + start) (stop - start) ⟨true, false, false⟩

/-- A library and all that it needs: mapped, known of, relocated and with its initializers noted, those of what it needs before its own. -/
private partial def loadOne (machine : Machine) (path : String) (space : Nat) (search : List String) (resolve : String → Option Nat)
    (ignoreMissing : Bool) (loading : IO.Ref Loading) : IO LoadedLibrary := do
  let architecture := machine.architecture
  let emu := machine.emu
  let some existing := (spaceHas space (← machine.libraries.get)).find? (fun library => library.path == path)
    | do
      let kernel ← machine.kernel.get
      let data ← match fileOf kernel path with
        | .ok data => pure data
        | .error errno => throw <| IO.userError s!"{path}: error {errno}"
      let program ← IO.ofExcept (Elf.parse data)
      unless program.relocatable do throw <| IO.userError s!"{path} isn't a library that can go anywhere"
      unless sameMachine architecture program do
        throw <| IO.userError s!"{path} is of ELF machine {program.machine} of {program.bits} bits, which isn't this machine"
      let image ← IO.ofExcept (Image.Elf.decode data)
      let (base, start, span) ← mapLibrary machine path data program
      let dynamic ← IO.ofExcept (Image.Elf.allDynamicSymbols image)
      let symbols := dynamic.filterMap fun symbol =>
        -- Those that it defines, of a type that has an address, and not those of thread-local storage.
        if symbol.sectionIndex != 0 && symbol.typ != 6 && !symbol.name.isEmpty && symbol.binding != 0 then
          some (symbol.name, base + symbol.value)
        else none
      let tags := Image.Elf.dynamicTagsOf image
      let name := ((tags.find? (·.1 == 14)).bind fun tag => Image.Elf.dynamicText image tag.2).getD (baseName path)
      let runPaths := tags.filterMap fun tag =>
        if tag.1 == 15 || tag.1 == 29 then Image.Elf.dynamicText image tag.2 else none
      let runPaths := runPaths.flatMap (·.splitOn ":")
      let origin := "/" ++ "/".intercalate ((path.splitOn "/").dropLast.filter (· != ""))
      let library : LoadedLibrary := { path, name, base, start, span, symbols, needs := [] }
      -- It is known of before what it needs is loaded, as they may need each other.
      machine.libraries.modify fun table => table.insert space (spaceHas space table ++ [library])
      loading.modify fun state => { state with mapped := library :: state.mapped }
      let needs ← (Elf.needed data).filterMapM fun needed => do
        match ← findLibrary machine needed origin runPaths search with
        | some found => pure (some (← loadOne machine found space search resolve ignoreMissing loading).path)
        | none =>
          if ignoreMissing then pure none
          else throw <| IO.userError s!"{path} needs {needed}, which isn't in this machine"
      -- Relocated with all there is to find.
      let table ← machine.libraries.get
      let scope := spaceHas space table
      let is64 := architecture.bits == 64
      let word := architecture.bits / 8
      let big := architecture.big
      let machineNumber := program.machine
      let lookup (symbol : Image.Elf.DynamicSymbol) : Except String Nat :=
        let unversioned := (symbol.name.splitOn "@").headD symbol.name
        match scope.findSome? (fun library => library.symbols.lookup unversioned), resolve unversioned with
        | some address, _ => .ok address
        | none, some address => .ok address
        | none, none =>
          -- Not found and it has its own, which is local, or it may go without.
          if symbol.sectionIndex != 0 then .ok (base + symbol.value)
          else if symbol.binding == 2 then .ok 0
          else .error unversioned
      let symbolList := dynamic.toArray
      let readWord (address : Nat) : IO Nat := do
        let bytes ← Bap.Emu.read emu address word
        pure ((if big then bytes.toList else bytes.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0)
      let writeWord (address value : Nat) : IO Unit := Bap.Emu.write emu address (numberBytes big word (value % 2 ^ architecture.bits))
      let relocations ← IO.ofExcept (Image.Elf.allDynamicRelocations image)
      let mut missing : List String := []
      let mut indirect : List (Nat × Nat) := []
      for relocation in relocations do
        let place := base + relocation.offset
        let symbolEntry : Option Image.Elf.DynamicSymbol := if relocation.symbol == 0 then none else symbolList[relocation.symbol]?
        let addend ← if relocation.explicitAddend then pure relocation.addend else
          match relocationKind machineNumber relocation.typ is64 with
          | .relative | .absolute | .indirect => readWord place
          | _ => pure 0
        match relocationKind machineNumber relocation.typ is64 with
        | .none => pure ()
        | .unknown => throw <| IO.userError s!"{path} has a relocation of type {relocation.typ}, which this can't do"
        | .threadLocal => throw <| IO.userError s!"{path} uses thread-local storage, whose offsets are those of a libc that isn't here"
        | .relative => writeWord place (base + addend)
        | .indirect => indirect := (place, base + addend) :: indirect
        | kind =>
          match symbolEntry, kind with
          | none, _ =>
            -- REL32 of MIPS without a symbol is relative.
            writeWord place (base + addend)
          | some symbol, _ =>
            if symbol.typ == 10 && symbol.sectionIndex != 0 then
              indirect := (place, base + symbol.value) :: indirect
            else
              match lookup symbol with
              | .ok address =>
                match kind with
                | .slot => writeWord place (address + (if relocation.explicitAddend then relocation.addend else 0))
                | _ => writeWord place (address + addend)
              | .error name => unless missing.contains name do missing := name :: missing
      -- The GOT of MIPS, which has no relocations: its local entries are moved, and the rest are its symbols from where the table says.
      if architecture matches .mips .. then
        let tag (key : Nat) : Option Nat := (tags.find? (·.1 == key)).map (·.2)
        if let (some got, some locals) := (tag 3, tag 0x7000000a) then
          for index in [0:locals] do
            let place := base + got + index * word
            writeWord place ((← readWord place) + base)
          if let (some first, some total) := (tag 0x70000013, tag 0x70000011) then
            for index in [first:total] do
              let place := base + got + (locals + index - first) * word
              let symbol := symbolList[index]?
              match symbol with
              | some symbol =>
                match lookup symbol with
                | .ok address => writeWord place address
                | .error name => unless missing.contains name do missing := name :: missing
              | none => pure ()
      unless missing.isEmpty do
        throw <| IO.userError s!"{path} needs what isn't there: {" ".intercalate missing.reverse}"
      -- What chooses an implementation runs now, with all that it could call relocated, as far as they can be.
      for (place, resolver) in indirect.reverse do
        writeWord place (← machine.call resolver [])
      protectLibrary machine image base program
      -- Its initializers, and what undoes them.
      let tagged (key : Nat) : Option Nat := (tags.find? (·.1 == key)).map (·.2)
      let arrayOf (start size : Nat) : IO (List Nat) := do
        match tagged start, tagged size with
        | some address, some bytes =>
          (List.range (bytes / word)).filterMapM fun index => do
            let value ← readWord (base + address + index * word)
            -- 0 and all ones mean nothing, as linkers have them.
            pure (if value == 0 || value == 2 ^ architecture.bits - 1 then none else some value)
        | _, _ => pure []
      let single (key : Nat) : List Nat := (tagged key).toList.map (base + ·)
      let initializers := single 12 ++ (← arrayOf 25 27)
      let finalizers := (← arrayOf 26 28).reverse ++ single 13
      loading.modify fun state => { state with initializers := state.initializers ++ initializers }
      -- What a resolver chooses is what it is to anyone who asks for it.
      let chosen ← dynamic.filterMapM fun symbol => do
        if symbol.typ == 10 && symbol.sectionIndex != 0 && symbol.binding != 0 && !symbol.name.isEmpty then
          pure (some (symbol.name, ← machine.call (base + symbol.value) []))
        else pure none
      let symbols := symbols.map fun entry => (entry.1, (chosen.lookup entry.1).getD entry.2)
      let finished : LoadedLibrary := { library with needs, finalizers, symbols }
      -- What it needs is held by it already, as each was counted when it was found.
      machine.libraries.modify fun table => table.insert space ((spaceHas space table).map fun other =>
        if other.path == path then finished else other)
      pure finished
  machine.libraries.modify fun table => table.insert space ((spaceHas space table).map fun other =>
    if other.path == path then { other with references := other.references + 1 } else other)
  pure existing

/-- Loads a shared library from the files of the machine, with all that it needs, into the process that runs, and runs its initializers,
as `dlopen`. What it imports is found in what is loaded, in the order that it was, and then by `resolve`, which is for what a host wants
to give it, such as a stub. A weak one that nowhere has is 0, and one that isn't is an error, with nothing left of the load. A library
that is here already just has one more hold on it. `ignoreMissing` goes on without a library that it needs, which only works if `resolve`
has what that would have given. Libraries that are named look in `search`, then its own `DT_RUNPATH`, then where libraries are. -/
def Machine.loadLibrary (machine : Machine) (path : String) (search : List String := []) (resolve : String → Option Nat := fun _ => none)
    (ignoreMissing : Bool := false) (runInitializers : Bool := true) : IO LoadedLibrary := do
  if ← machine.emu.serving.get then
    throw <| IO.userError "a library can't be loaded in the middle of an instruction: stop the thread, and load it once the run returns"
  let some found ← findLibrary machine path "/" [] search
    | throw <| IO.userError s!"{path} isn't in this machine"
  let space := (← currentTask machine.emu).space
  let before ← machine.libraries.get
  let loading ← IO.mkRef ({} : Loading)
  let undo : IO Unit := do
    for library in (← loading.get).mapped do
      unmap machine.emu library.start library.span
    machine.libraries.set before
  try
    let library ← loadOne machine found space search resolve ignoreMissing loading
    if runInitializers then
      for initializer in (← loading.get).initializers do
        let _ ← machine.call initializer []
    pure library
  catch error =>
    undo
    throw error

/-- Where a symbol is, in that library if one is given, and otherwise in what is loaded in the process that runs, as `dlsym`. -/
def Machine.findSymbol (machine : Machine) (name : String) (library : Option LoadedLibrary := none) : IO (Option Nat) := do
  let space := (← currentTask machine.emu).space
  let loaded : List LoadedLibrary := spaceHas space (← machine.libraries.get)
  let scope : List LoadedLibrary := match library with
    | some wanted => loaded.filter fun other => other.path == wanted.path
    | none => loaded
  pure (scope.findSome? fun other => other.symbols.lookup name)

/-- What is loaded in the process that runs, in the order that a symbol is looked for in them. -/
def Machine.loadedLibraries (machine : Machine) : IO (List LoadedLibrary) := do
  pure (spaceHas (← currentTask machine.emu).space (← machine.libraries.get))

/-- Lets go of a library, as `dlclose`: when nothing holds on to it, its finalizers run, it is unmapped and it lets go of what it needs. -/
partial def Machine.unloadLibrary (machine : Machine) (library : LoadedLibrary) : IO Unit := do
  let space := (← currentTask machine.emu).space
  let some current := (spaceHas space (← machine.libraries.get)).find? (·.path == library.path)
    | throw <| IO.userError s!"{library.path} isn't loaded"
  if current.references > 1 then
    machine.libraries.modify fun table => table.insert space ((spaceHas space table).map fun other =>
      if other.path == library.path then { other with references := other.references - 1 } else other)
  else
    for finalizer in current.finalizers do
      let _ ← machine.call finalizer []
    unmap machine.emu current.start current.span
    machine.libraries.modify fun table => table.insert space ((spaceHas space table).filter (·.path != library.path))
    for needed in current.needs do
      if let some other := (spaceHas space (← machine.libraries.get)).find? (·.path == needed) then
        machine.unloadLibrary other

end Bap.Linux
