import Bap.Image.Basic
import Bap.Core.Sexp

namespace Bap.Image.Ogre

inductive Field where
  | arch (name : String)
  | bits (width : Nat)
  | littleEndian (value : Bool)
  | entryPoint (address : Nat)
  | section (value : Section)
  | segment (value : Segment)
  | symbol (value : Symbol)
  | codeRegion (address size offset : Nat)
  deriving DecidableEq, Repr

structure Doc where
  fields : List Field := []
  deriving DecidableEq, Repr

private def archName : Arch → String
  | .x86 => "i386"
  | .x86_64 => "amd64"
  | .arm => "arm"
  | .aarch64 => "aarch64"
  | .mips => "mips"
  | .powerpc => "powerpc"
  | .riscv => "riscv"
  | .systemz => "systemz"
  | .unknown => "unknown"

private def decodeArch (name : String) : Except String Arch :=
  match name with
  | "i386" | "x86" => .ok .x86
  | "amd64" | "x86_64" => .ok .x86_64
  | "arm" => .ok .arm
  | "aarch64" => .ok .aarch64
  | "mips" => .ok .mips
  | "powerpc" => .ok .powerpc
  | "riscv" => .ok .riscv
  | "systemz" => .ok .systemz
  | "unknown" => .ok .unknown
  | _ => .error s!"unknown Ogre architecture {name}"

private def nat (value : Nat) : Sexp := .atom (toString value)
private def bool (value : Bool) : Sexp := .atom (toString value)

private def boolValue (input : Sexp) : Except String Bool := do
  match ← Sexp.asAtom input with
  | "true" => .ok true
  | "false" => .ok false
  | _ => .error "invalid Ogre boolean"

private def encodeField : Field → List Sexp
  | .arch name => [.tagged "arch" [.atom name]]
  | .bits width => [.tagged "bits" [nat width]]
  | .littleEndian value => [.tagged "is-little-endian" [bool value]]
  | .entryPoint address => [.tagged "entry-point" [nat address]]
  | .section sec =>
    let region := [nat sec.addr, nat sec.size]
    [
      .tagged "section" region,
      .tagged "named-region" (region ++ [.atom sec.name]),
      .tagged "section-record" [.atom sec.name, nat sec.addr, nat sec.offset,
        nat sec.size, nat sec.flags, nat sec.kind]
    ]
  | .segment segment =>
    let region := [nat segment.addr, nat segment.size]
    [
      .tagged "segment" (region ++ [bool segment.readable, bool segment.writable, bool segment.executable]),
      .tagged "named-region" (region ++ [.atom segment.name]),
      .tagged "segment-record" [.atom segment.name, nat segment.addr, nat segment.size,
        bool segment.readable, bool segment.writable, bool segment.executable]
    ]
  | .symbol symbol =>
    [
      .tagged "named-symbol" [nat symbol.addr, .atom symbol.name],
      .tagged "symbol-chunk" [nat symbol.addr, nat symbol.size, nat symbol.addr],
      .tagged "symbol-record" [.atom symbol.name, nat symbol.addr, nat symbol.size,
        bool symbol.isFunction, bool symbol.isDebug, bool symbol.thumb]
    ]
  | .codeRegion address size offset => [.tagged "code-region" [nat address, nat size, nat offset]]

private def decodeSection (args : List Sexp) : Except String Field := do
  match args with
  | [name, addr, offset, size, flags, kind] =>
    .ok (.section ⟨← Sexp.asAtom name, ← Sexp.nat addr, ← Sexp.nat offset,
      ← Sexp.nat size, ← Sexp.nat flags, ← Sexp.nat kind⟩)
  | _ => .error "invalid Ogre section record"

private def decodeSegment (args : List Sexp) : Except String Field := do
  match args with
  | [name, addr, size, readable, writable, executable] =>
    .ok (.segment ⟨← Sexp.asAtom name, ← Sexp.nat addr, ← Sexp.nat size,
      ← boolValue readable, ← boolValue writable, ← boolValue executable⟩)
  | _ => .error "invalid Ogre segment record"

private def decodeSymbol (args : List Sexp) : Except String Field := do
  match args with
  | [name, addr, size, isFunction, isDebug, thumb] =>
    .ok (.symbol ⟨← Sexp.asAtom name, ← Sexp.nat addr, ← Sexp.nat size,
      ← boolValue isFunction, ← boolValue isDebug, ← boolValue thumb⟩)
  | _ => .error "invalid Ogre symbol record"

private def decodeFact (fact : Sexp) : Except String (List Field) := do
  let items ← Sexp.asList fact
  match items with
  | .atom "arch" :: [name] => .ok [.arch (← Sexp.asAtom name)]
  | .atom "bits" :: [width] => .ok [.bits (← Sexp.nat width)]
  | .atom "is-little-endian" :: [value] => .ok [.littleEndian (← boolValue value)]
  | .atom "entry-point" :: [address] => .ok [.entryPoint (← Sexp.nat address)]
  | .atom "section-record" :: args => .ok [← decodeSection args]
  | .atom "segment-record" :: args => .ok [← decodeSegment args]
  | .atom "symbol-record" :: args => .ok [← decodeSymbol args]
  | .atom "code-region" :: [address, size, offset] =>
    .ok [.codeRegion (← Sexp.nat address) (← Sexp.nat size) (← Sexp.nat offset)]
  | .atom "section" :: _ | .atom "named-region" :: _ | .atom "segment" :: _ |
    .atom "named-symbol" :: _ | .atom "symbol-chunk" :: _ => .ok []
  | _ => .error s!"unsupported Ogre fact {fact}"

def ofImage (image : Image) : Doc := {
  fields :=
    [.arch (archName image.arch), .bits image.addrWidth, .littleEndian (image.endian = .little),
      .entryPoint image.entryPoint] ++
    image.sections.map Field.section ++
    image.segments.map Field.segment ++
    image.symbols.map Field.symbol ++
    image.memory.entries.map fun entry => .codeRegion entry.1.addr entry.1.size 0
}

def render (doc : Doc) : String :=
  toString (Sexp.list (doc.fields.flatMap encodeField))

def parse (input : String) : Except String Doc := do
  let input ← Sexp.parse input
  let facts ← Sexp.asList input
  let fields ← facts.mapM decodeFact
  .ok ⟨fields.flatten⟩

def toImage (doc : Doc) : Except String Image := do
  let arch ← match doc.fields.find? fun field => match field with | .arch _ => true | _ => false with
    | some (.arch name) => decodeArch name
    | _ => .error "Ogre document has no architecture"
  let width ← match doc.fields.find? fun field => match field with | .bits _ => true | _ => false with
    | some (.bits width) => .ok width
    | _ => .error "Ogre document has no address width"
  let little ← match doc.fields.find? fun field => match field with | .littleEndian _ => true | _ => false with
    | some (.littleEndian value) => .ok value
    | _ => .error "Ogre document has no endianness"
  let entry ← match doc.fields.find? fun field => match field with | .entryPoint _ => true | _ => false with
    | some (.entryPoint entry) => .ok entry
    | _ => .error "Ogre document has no entry point"
  let sections := doc.fields.filterMap fun field => match field with | .section sec => some sec | _ => none
  let segments := doc.fields.filterMap fun field => match field with | .segment segment => some segment | _ => none
  let symbols := doc.fields.filterMap fun field => match field with | .symbol symbol => some symbol | _ => none
  let regions := doc.fields.filterMap fun field =>
    match field with
    | .codeRegion address size _ =>
      some (⟨address, ByteArray.mk (List.replicate size 0).toArray, true, false, true⟩ : MemRegion)
    | _ => none
  let memory : MemoryMap Unit := regions.foldl (init := MemoryMap.empty) fun memory region => memory.add region ()
  .ok {
    arch
    addrWidth := width
    endian := if little then .little else .big
    entryPoint := entry
    data := ByteArray.empty
    sections
    segments
    symbols
    memory
  }

end Bap.Image.Ogre
