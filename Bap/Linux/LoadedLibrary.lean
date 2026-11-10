import Bap.Linux.Wire
import Std.Data.HashMap

/-! What a machine has loaded of shared libraries from outside its programs, as plain data, which goes in a checkpoint. -/

namespace Bap.Linux

/-- What a library has of thread-local storage, as a libc needs it to give each thread a block: what its `PT_TLS` is, the number of its
module, and how far its block is from the rest, which is a distance above the thread pointer on most targets and below it on x86. -/
structure LibraryTls where
  module : Nat
  offset : Nat
  /-- Where what each thread starts with is, and how much. What is after that up to `memorySize` starts as zeros. -/
  image : Nat
  fileSize : Nat
  memorySize : Nat
  alignment : Nat
  deriving DecidableEq, Repr

/-- A shared library that `Machine.loadLibrary` loaded into a process: where it is, what it exports, what it needs, its thread-local
storage, what is to run when it goes, and the digest of its file, by which a checkpoint knows it. -/
structure LoadedLibrary where
  /-- What it is known by: its path in the machine. -/
  path : String
  /-- `DT_SONAME`, or the name of its file: what another library can ask for. -/
  name : String
  /-- What its addresses are off by. -/
  base : Nat
  /-- What is mapped for it. -/
  start : Nat
  span : Nat
  /-- What it defines, and where, by name, as it can be reached from outside. -/
  symbols : List (String × Nat)
  /-- What it holds on to, by path, for as long as it is here. -/
  needs : List String
  /-- How many hold on to it, of `loadLibrary` and of others that need it. -/
  references : Nat := 1
  /-- What to call when it goes, in that order. -/
  finalizers : List Nat := []
  /-- Its thread-local storage, if it has any, and what is in it by name, at an offset in its block. -/
  tls : Option LibraryTls := none
  tlsSymbols : List (String × Nat) := []
  /-- What its file was, by `targetDigest`, to know it by whatever path it has. -/
  digest : Nat := 0
  /-- Its initializers, in the order that they run, and whether they all have. -/
  initializers : List Nat := []
  initialized : Bool := false
  /-- What it defines that has a version, by name and the name of the version, of the default and of the others: what was linked to one
  is bound to it. -/
  versions : List ((String × String) × Nat) := []
  deriving DecidableEq, Repr

namespace LoadedLibrary

open Wire

private def putSymbol (out : ByteArray) (symbol : String × Nat) : ByteArray := putNat (putText out symbol.1) symbol.2

private def getSymbol : Decoder (String × Nat) := fun data at_ => do
  let (name, at_) ← getText data at_
  let (address, at_) ← getNat data at_
  .ok ((name, address), at_)

private def putLibrary (out : ByteArray) (library : LoadedLibrary) : ByteArray :=
  let out := putText (putText out library.path) library.name
  let out := putNat (putNat (putNat out library.base) library.start) library.span
  let out := putList putSymbol out library.symbols
  let out := putList putText out library.needs
  let out := putNat out library.references
  let out := putList putNat out library.finalizers
  let out := putOption (fun out tls =>
    putNat (putNat (putNat (putNat (putNat (putNat out tls.module) tls.offset) tls.image) tls.fileSize) tls.memorySize) tls.alignment) out library.tls
  let out := putList putSymbol out library.tlsSymbols
  let out := putList putNat (putNat out library.digest) library.initializers
  let out := putFlag out library.initialized
  putList (fun out ((name, version), address) => putNat (putText (putText out name) version) address) out library.versions

private def getLibrary : Decoder LoadedLibrary := fun data at_ => do
  let (path, at_) ← getText data at_
  let (name, at_) ← getText data at_
  let (base, at_) ← getNat data at_
  let (start, at_) ← getNat data at_
  let (span, at_) ← getNat data at_
  let (symbols, at_) ← getList getSymbol data at_
  let (needs, at_) ← getList getText data at_
  let (references, at_) ← getNat data at_
  let (finalizers, at_) ← getList getNat data at_
  let (tls, at_) ← getOption (fun data at_ => do
    let (module, at_) ← getNat data at_
    let (offset, at_) ← getNat data at_
    let (image, at_) ← getNat data at_
    let (fileSize, at_) ← getNat data at_
    let (memorySize, at_) ← getNat data at_
    let (alignment, at_) ← getNat data at_
    .ok ({ module, offset, image, fileSize, memorySize, alignment : LibraryTls }, at_)) data at_
  let (tlsSymbols, at_) ← getList getSymbol data at_
  let (digest, at_) ← getNat data at_
  let (initializers, at_) ← getList getNat data at_
  let (initialized, at_) ← getFlag data at_
  let (versions, at_) ← getList (fun data at_ => do
    let (name, at_) ← getText data at_
    let (version, at_) ← getText data at_
    let (address, at_) ← getNat data at_
    .ok (((name, version), address), at_)) data at_
  .ok ({ path, name, base, start, span, symbols, needs, references, finalizers, tls, tlsSymbols, digest, initializers, initialized,
         versions }, at_)

private def putEntry (out : ByteArray) (entry : Nat × List LoadedLibrary) : ByteArray :=
  putList putLibrary (putNat out entry.1) entry.2

private def getEntry : Decoder (Nat × List LoadedLibrary) := fun data at_ => do
  let (space, at_) ← getNat data at_
  let (libraries, at_) ← getList getLibrary data at_
  .ok ((space, libraries), at_)

/-- Those of a machine, by address space: in each, in the order that a symbol is looked for in them. -/
def encode (table : Std.HashMap Nat (List LoadedLibrary)) : ByteArray :=
  putSorted putEntry ByteArray.empty table.toList

/-- What `encode` made, or why it isn't. -/
def decode (data : ByteArray) : Except String (Std.HashMap Nat (List LoadedLibrary)) := do
  let (entries, at_) ← getList getEntry data 0
  expectEnd data at_
  .ok (Std.HashMap.ofList entries)

end LoadedLibrary

end Bap.Linux
