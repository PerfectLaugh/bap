import Bap.Linux.Machine
import Bap.Image.Elf

/-! Shared libraries loaded into a machine from outside it, as `dlopen`, `dlsym` and `dlclose` would be from inside: without a libc or a
dynamic linker in the guest, for what wants to call a library in a guest, such as the native code of an Android application. What a
program loads for itself is another thing, and goes as it does on Linux, by its own `PT_INTERP`.

Everything is bound when it is loaded. A relocation that this doesn't know is an error and not something to leave undone.

Thread-local storage is laid out as a dynamic linker lays it out for what is there when a program starts: each library that has it has a
number and an offset, and its relocations say those. Who gives a thread its block and its thread pointer is who runs: a libc, by what
`LoadedLibrary.tls` says, or `Machine.setupThreadTls` where there is none. Nothing here touches the thread pointer until that is asked for.
A descriptor of TLS is on x86 and AArch64, as this has the function that it needs only for those. -/

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

/-- What code at the page that calls return to does for a descriptor of TLS whose argument is already what is wanted: it gives that back. -/
private def tlsDescriptorCode : Architecture → Option ByteArray
  | .x86_64 => some (ByteArray.mk #[0x48, 0x8B, 0x40, 0x08, 0xC3])
  | .i686 => some (ByteArray.mk #[0x8B, 0x40, 0x04, 0xC3])
  | .aarch64 => some (ByteArray.mk #[0x00, 0x04, 0x40, 0xF9, 0xC0, 0x03, 0x5F, 0xD6])
  | _ => none

/-- Where the code of a descriptor of TLS is in that page. -/
private def tlsDescriptorOffset : Nat := 16

/-- That page, once something wants it. -/
private def Machine.ensureReturnPage (machine : Machine) : IO Nat := do
  let page := callReturnPage machine
  if (lookupRegion (← machine.emu.regions.get) page).isNone then
    let code := (tlsDescriptorCode machine.architecture).getD ByteArray.empty
    let bytes := ByteArray.mk (Array.replicate tlsDescriptorOffset 0) ++ code
    Bap.Emu.map machine.emu ⟨page, bytes ++ ByteArray.mk (Array.replicate (4096 - bytes.size) 0), ⟨true, false, true⟩⟩
  pure page

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
  let returnTo ← machine.ensureReturnPage
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
        -- What the host gives it, which is as much a source as what a system call gives.
        for starts in ← emu.hostStarts.get do starts "Machine.call"
        for ends in ← emu.hostEnds.get do ends (some name)
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
  /-- The number of a module, its offset, what that is from a thread pointer, as x86 has that the other way round, and a descriptor. -/
  | tlsModule
  | tlsOffset
  | tlsPointer
  | tlsPointerNegated
  | tlsDescriptor
  | unknown

private def relocationKind (machine typ : Nat) (is64 : Bool) : RelocationKind :=
  let types (none relative indirect absolute slot : List Nat) (module offset pointer : List Nat) (descriptor : List Nat := [])
      (negated : List Nat := []) : RelocationKind :=
    if none.contains typ then .none
    else if relative.contains typ then .relative
    else if indirect.contains typ then .indirect
    else if absolute.contains typ then .absolute
    else if slot.contains typ then .slot
    else if module.contains typ then .tlsModule
    else if offset.contains typ then .tlsOffset
    else if pointer.contains typ then .tlsPointer
    else if negated.contains typ then .tlsPointerNegated
    else if descriptor.contains typ then .tlsDescriptor
    else .unknown
  match machine with
  | 62 => types [0] [8] [37] [1] [6, 7] [16] [17] [18] [36]
  | 3 => types [0] [8] [42] [1] [6, 7] [35] [36] [14] [41] [37]
  | 183 => types [0] [1027] [1032] [257] [1025, 1026] [1028] [1029] [1030] [1031]
  | 40 => types [0] [23] [160] [2] [21, 22] [17] [18] [19]
  | 243 => types [0] [3] [58] [if is64 then 2 else 1] [5] [if is64 then 7 else 6] [if is64 then 9 else 8] [if is64 then 11 else 10]
  | 20 | 21 => types [0] [22] [248] [if machine == 20 then 1 else 38] [20, 21] [68] [78] [73]
  -- REL32 has a symbol or doesn't, and with MIPS64 what is stacked on it is only how wide it is.
  | 8 => match typ % 256 with
    | 0 => .none
    | 3 => .absolute
    | 38 | 40 => .tlsModule
    | 39 | 41 => .tlsOffset
    | 47 | 48 => .tlsPointer
    | _ => .unknown
  | _ => .unknown

/-- Whether thread-local storage is below the thread pointer. -/
private def tlsBelow : Architecture → Bool
  | .x86_64 | .i686 => true
  | _ => false

/-- What is between the thread pointer and the first block, for those where they are above it. -/
private def tlsGap : Architecture → Nat
  | .aarch64 => 16
  | .arm => 8
  | _ => 0

/-- How far a thread pointer is past where those above it start: it points in the middle, to reach more with what an instruction has. -/
private def tlsPointerBias : Architecture → Nat
  | .mips .. | .powerpc .. => 0x7000
  | _ => 0

/-- What a module's offset is relative to, in what `__tls_get_addr` is given. -/
private def tlsOffsetBias : Architecture → Nat
  | .riscv64 | .riscv32 => 0x800
  | .mips .. | .powerpc .. => 0x8000
  | _ => 0

private def alignUp (value alignment : Nat) : Nat :=
  let alignment := max alignment 1
  (value + alignment - 1) / alignment * alignment

/-- Where the next module goes, after these. -/
private def nextTlsOffset (architecture : Architecture) (loaded : List LoadedLibrary) (memorySize alignment : Nat) : Nat :=
  if tlsBelow architecture then
    let used := loaded.foldl (fun used library => max used ((library.tls.map (·.offset)).getD 0)) 0
    alignUp (used + memorySize) alignment
  else
    let used := loaded.foldl (fun used library =>
      max used ((library.tls.map fun tls => tls.offset + tls.memorySize).getD 0)) (tlsGap architecture)
    alignUp used alignment

/-- How far a byte of a module's block is from a thread pointer, as what is added to it. It wraps as a word does, as it can be below it. -/
private def tlsPointerValue (architecture : Architecture) (tls : LibraryTls) (value : Nat) : Nat :=
  let modulus := 2 ^ architecture.bits
  if tlsBelow architecture then (value + modulus - tls.offset) % modulus
  else (value + tls.offset + modulus - tlsPointerBias architecture) % modulus

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

/-- Maps a library, writable and executable until it has been relocated, so that its indirect resolvers can run. -/
private def mapLibrary (machine : Machine) (path : String) (data : ByteArray) (program : Elf.Program) : IO (Nat × Nat × Nat) := do
  let emu := machine.emu
  if program.segments.isEmpty then throw <| IO.userError s!"{path} has nothing to load"
  let lowest := program.segments.foldl (fun lowest segment => min lowest segment.address) (2 ^ 64)
  let highest := program.segments.foldl (fun highest segment => max highest (segment.address + segment.memorySize)) 0
  let first := lowest / 4096 * 4096
  let span := (highest + 4095) / 4096 * 4096 - first
  let start ← placeZeros emu 0 false span 7
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
      -- Its thread-local storage, after what is there.
      let tlsHeader := Image.Elf.programHeaderOf image 7
      let loadedNow := spaceHas space (← machine.libraries.get)
      let nextModule := loadedNow.foldl (fun next other => max next ((other.tls.map fun info => info.module + 1).getD next)) 1
      let tls : Option LibraryTls := tlsHeader.map fun header =>
        -- A header has no alignment here, and a block that has more than a word's goes by what its variables say.
        let alignment := Image.Elf.tlsAlignment image
        { module := nextModule, offset := nextTlsOffset architecture loadedNow header.memorySize alignment,
          image := base + header.addr, fileSize := header.fileSize, memorySize := header.memorySize, alignment }
      let tlsSymbols := dynamic.filterMap fun symbol =>
        if symbol.sectionIndex != 0 && symbol.typ == 6 && !symbol.name.isEmpty then some (symbol.name, symbol.value) else none
      let library : LoadedLibrary := { path, name, base, start, span, symbols, needs := [], tls, tlsSymbols, digest := targetDigest architecture data }
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
        let kind := relocationKind machineNumber relocation.typ is64
        match kind with
        | .none => pure ()
        | .unknown => throw <| IO.userError s!"{path} has a relocation of type {relocation.typ}, which this can't do"
        | .tlsModule | .tlsOffset | .tlsPointer | .tlsPointerNegated | .tlsDescriptor =>
          -- Of its own, or of what has that name, first in the order that symbols are looked for. One that is weak and nowhere is at
          -- nothing, of no module.
          let owner : Except String (Option (LibraryTls × Nat)) :=
            match symbolEntry with
            | none => .ok (tls.map fun info => (info, 0))
            | some symbol =>
              let unversioned := (symbol.name.splitOn "@").headD symbol.name
              let inOther (other : LoadedLibrary) : Option (LibraryTls × Nat) :=
                match other.tlsSymbols.lookup unversioned, other.tls with
                | some value, some info => some (info, value)
                | _, _ => none
              match scope.findSome? inOther with
              | some found => .ok (some found)
              | none =>
                if symbol.sectionIndex != 0 then .ok (tls.map fun info => (info, symbol.value))
                else if symbol.binding == 2 then .ok none
                else .error unversioned
          match owner with
          | .error name => unless missing.contains name do missing := name :: missing
          | .ok found =>
            let tlsAddend := if relocation.explicitAddend then relocation.addend else 0
            -- On MIPS these are slots of the GOT, which has nothing to add to a symbol: `ld.lld` leaves the value of that symbol there.
            let gotSlot := (architecture matches .mips ..) && symbolEntry.isSome
            let storedAddend ← if relocation.explicitAddend || gotSlot then pure 0 else
              -- A word of its own holds what is added, but for a module, which has nothing to add.
              match kind with
              | .tlsModule => pure 0
              | .tlsDescriptor => readWord (place + word)
              | _ => readWord place
            let plus := tlsAddend + storedAddend
            match kind, found with
            | .tlsModule, some (info, _) => writeWord place info.module
            | .tlsModule, none => writeWord place 0
            | .tlsOffset, some (_, value) => writeWord place (value + plus + 2 ^ architecture.bits - tlsOffsetBias architecture)
            | .tlsOffset, none => writeWord place 0
            | .tlsPointer, some (info, value) => writeWord place (tlsPointerValue architecture info (value + plus))
            | .tlsPointer, none => writeWord place 0
            | .tlsPointerNegated, some (info, value) => writeWord place (info.offset + 2 ^ architecture.bits - (value + plus))
            | .tlsPointerNegated, none => writeWord place 0
            | .tlsDescriptor, _ =>
              let some _ := tlsDescriptorCode architecture
                | throw <| IO.userError s!"{path} has a descriptor of thread-local storage, which this can't do on this target"
              let page ← machine.ensureReturnPage
              let value := match found with
                | some (info, value) => tlsPointerValue architecture info (value + plus)
                | none => 0
              writeWord place (page + tlsDescriptorOffset)
              writeWord (place + word) value
            | _, _ => pure ()
        | .relative => writeWord place (base + addend)
        | .indirect => indirect := (place, base + addend) :: indirect
        | _ =>
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
      -- A resolver is called as the kernel's loader calls it: on AArch64 with `AT_HWCAP` and `_IFUNC_ARG_HWCAP`, and what has
      -- `AT_HWCAP` and `AT_HWCAP2`, which is how one finds out what it may use.
      let callResolver (resolver : Nat) : IO Nat := do
        match architecture with
        | .aarch64 =>
          let process := (← machine.kernel.get).process (← currentTask emu).group
          let auxiliaryValue (key : Nat) : Nat :=
            ((List.range (process.auxiliary.length / 2)).findSome? fun index =>
              if process.auxiliary[2 * index]! == key then some process.auxiliary[2 * index + 1]! else none).getD 0
          let hwcap := auxiliaryValue 16
          let argument ← machine.calloc 1 24
          writeWord argument 24
          writeWord (argument + 8) hwcap
          writeWord (argument + 16) (auxiliaryValue 26)
          try machine.call resolver [hwcap + 2 ^ 62, argument]
          finally machine.free argument
        | _ => machine.call resolver []
      -- What chooses an implementation runs now, with all that it could call relocated, as far as they can be.
      for (place, resolver) in indirect.reverse do
        writeWord place (← callResolver resolver)
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
          pure (some (symbol.name, ← callResolver (base + symbol.value)))
        else pure none
      let symbols := symbols.map fun entry => (entry.1, (chosen.lookup entry.1).getD entry.2)
      let finished : LoadedLibrary := { library with needs, finalizers, symbols, initializers }
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
      -- They have all run, of what this loaded.
      let loaded := (← loading.get).mapped.map (·.path)
      machine.libraries.modify fun table => table.insert space ((spaceHas space table).map fun other =>
        if loaded.contains other.path then { other with initialized := true } else other)
    pure ((spaceHas space (← machine.libraries.get)).find? (·.path == library.path) |>.getD library)
  catch error =>
    undo
    throw error

/-- Where a byte of a library's thread-local storage is, for a thread with this thread pointer. -/
def Machine.threadLocalAddress (machine : Machine) (tls : LibraryTls) (threadPointer : Nat) (value : Nat := 0) : Nat :=
  (threadPointer + tlsPointerValue machine.architecture tls value) % 2 ^ machine.architecture.bits

/-- Gives the thread that runs a block of thread-local storage for what is loaded, and makes it the thread pointer, and says what that is,
for when there is no libc to do it. Whatever a thread had of its own is left behind. `reserved` is what is kept free next to it, for a
libc's use: below a block that is above the thread pointer, and above one that is below. Each thread needs one of its own. -/
def Machine.setupThreadTls (machine : Machine) (reserved : Nat := 256) : IO Nat := do
  let architecture := machine.architecture
  let space := (← currentTask machine.emu).space
  let loaded : List LoadedLibrary := spaceHas space (← machine.libraries.get)
  let modules := loaded.filterMap (·.tls)
  let strictest := modules.foldl (fun strictest tls => max strictest tls.alignment) 64
  let width := architecture.bits
  let (_, register) := threadRegisters machine.emu.config.syscallAbi
  let blockSize := if tlsBelow architecture then
      modules.foldl (fun size tls => max size tls.offset) 0
    else
      modules.foldl (fun size tls => max size (tls.offset + tls.memorySize)) (tlsGap architecture)
  let total := blockSize + reserved + 2 * strictest + tlsPointerBias architecture
  let block ← machine.calloc 1 total
  let threadPointer :=
    if tlsBelow architecture then alignUp (block + blockSize) strictest
    else alignUp (block + reserved) strictest + tlsPointerBias architecture
  for tls in modules do
    let image ← Bap.Emu.read machine.emu tls.image tls.fileSize
    machine.write (machine.threadLocalAddress tls threadPointer) image
  setReg machine.emu ⟨register, .imm width, 0, false⟩ (.bits (BitVec.ofNat width threadPointer))
  pure threadPointer

/-- Where a symbol is, in that library if one is given, and otherwise in what is loaded in the process that runs, as `dlsym`. -/
def Machine.findSymbol (machine : Machine) (name : String) (library : Option LoadedLibrary := none) : IO (Option Nat) := do
  let space := (← currentTask machine.emu).space
  let loaded : List LoadedLibrary := spaceHas space (← machine.libraries.get)
  let scope : List LoadedLibrary := match library with
    | some wanted => loaded.filter fun other => other.path == wanted.path
    | none => loaded
  pure (scope.findSome? fun other => other.symbols.lookup name)

/-- Where a symbol is in a loaded file, including one that isn't exported for dynamic linking. -/
def Machine.findStaticSymbol (machine : Machine) (name : String) (library : Option LoadedLibrary := none) : IO (Option Nat) := do
  let space := (← currentTask machine.emu).space
  let loaded : List LoadedLibrary := spaceHas space (← machine.libraries.get)
  let scope : List LoadedLibrary := match library with
    | some wanted => loaded.filter fun other => other.path == wanted.path
    | none => loaded
  for other in scope do
    match fileOf (← machine.kernel.get) other.path with
    | .error _ => pure ()
    | .ok data =>
      match Image.Elf.decode data with
      | .error _ => pure ()
      | .ok image =>
        match image.symbols.find? fun symbol => symbol.name == name && symbol.addr != 0 with
        | some symbol => return some (other.base + symbol.addr)
        | none => pure ()
  return none

/-- What is loaded in the process that runs, in the order that a symbol is looked for in them. -/
def Machine.loadedLibraries (machine : Machine) : IO (List LoadedLibrary) := do
  pure (spaceHas (← currentTask machine.emu).space (← machine.libraries.get))

/-- What every process has loaded with `loadLibrary`: by address space, each library with where it is, what its file was and whether its initializers have run. -/
def Machine.manifest (machine : Machine) : IO (List (Nat × LoadedLibrary)) := do
  let table ← machine.libraries.get
  let spaces := (table.toList.map (·.1)).toArray.qsort (· < ·) |>.toList
  pure (spaces.flatMap fun space => (spaceHas space table).map (space, ·))

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
