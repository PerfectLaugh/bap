import Bap.Linux.Calls
import Bap.Linux.Elf
import Bap.Linux.Image

/-! What the virtual kernel says of itself. That it can't reach the machine it runs on needs no theorem: its operations are pure
functions of its state, which their types say. -/

namespace Bap.Linux

open Kernel

@[simp] private theorem process_setProcess_same (kernel : Kernel) (group : Nat) (value : Process) :
    (kernel.setProcess group value).process group = value := by
  simp [Kernel.process, Kernel.setProcess]

private theorem process_setProcess_other (kernel : Kernel) {group other : Nat} (value : Process) (h : group ≠ other) :
    (kernel.setProcess group value).process other = kernel.process other := by
  simp [Kernel.process, Kernel.setProcess, Std.HashMap.getD_insert, h]

/-- A descriptor that was closed is gone, so nothing can read it. -/
theorem read_after_close {kernel next : Kernel} {group fd : Nat} (h : kernel.close group fd = .ok next) (count : Nat) :
    next.read group fd count = .error Errno.ebadf := by
  simp only [Kernel.close] at h
  by_cases hopen : (kernel.process group).descriptors.contains fd = true
  · simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    simp [Kernel.read, Kernel.openFileOf, bind, Except.bind]
  · simp [hopen, bind, Except.bind] at h

/-- A child starts with the descriptors, the directory and the break of its parent. -/
theorem fork_process (kernel : Kernel) (parent child : Nat) : (kernel.fork parent child).process child = kernel.process parent := by
  simp [Kernel.fork]

/-- What a child does to its own table leaves that of its parent alone. -/
theorem setProcess_isolated (kernel : Kernel) {child parent : Nat} (value : Process) (h : child ≠ parent) :
    (kernel.setProcess child value).process parent = kernel.process parent :=
  process_setProcess_other kernel value h

/-- Bytes of `Abi` have the size that they say. -/
@[simp] theorem bytesOf_size (size value : Nat) : (Abi.bytesOf size value).size = size := by
  simp [Abi.bytesOf, ByteArray.size]

/-- A field has the size that it says, in either order. -/
@[simp] theorem field_size (big : Bool) (size value : Nat) : (Abi.field big size value).size = size := by
  unfold Abi.field
  cases big
  · exact bytesOf_size size value
  · exact (Array.size_reverse ..).trans (bytesOf_size size value)

/-- `struct stat` has its 144 bytes, whatever is in it. -/
theorem stat_size (value : Kernel.Stat) : (Abi.stat value).size = 144 := by
  simp [Abi.stat, ByteArray.size_append]

/-- `struct statx` has its 256 bytes, whatever is in it. -/
theorem statx_size (value : Kernel.Stat) : (Abi.statx value).size = 256 := by
  simp [Abi.statx, ByteArray.size_append]

/-- `struct timespec` has its 16 bytes. -/
theorem time_size (now scale : Nat) : (Abi.time now scale).size = 16 := by
  simp [Abi.time, ByteArray.size_append]

/-- `struct stat` of `asm-generic` has its 128 bytes, whatever is in it. -/
theorem genericStat_size (value : Kernel.Stat) : (Abi.genericStat value).size = 128 := by
  simp [Abi.genericStat, ByteArray.size_append]

/-- No number of x86-64 means two calls, so that the order of the table doesn't matter. -/
theorem x86_64Calls_nodup : (x86_64Calls.map (·.1)).Nodup := by decide +kernel

/-- No number of `asm-generic` means two calls. -/
theorem genericCalls_nodup : (genericCalls.map (·.1)).Nodup := by decide +kernel

/-- No number of 32-bit `asm-generic` means two calls. -/
theorem generic32Calls_nodup : (generic32Calls.map (·.1)).Nodup := by decide +kernel

/-- No number of o32 means two calls. -/
theorem o32Calls_nodup : (o32Calls.map (·.1)).Nodup := by decide +kernel

/-- No number of PowerPC means two calls. -/
theorem powerpcCalls_nodup : (powerpcCalls.map (·.1)).Nodup := by decide +kernel

/-- No number of n64 means two calls. -/
theorem n64Calls_nodup : (n64Calls.map (·.1)).Nodup := by decide +kernel

/-- `struct stat` of 64-bit MIPS has its 160 bytes, in either order. -/
theorem mips64Stat_size (value : Kernel.Stat) (big : Bool) : (Abi.mips64Stat value big).size = 160 := by
  simp [Abi.mips64Stat, ByteArray.size_append]

/-- Translating the flags of `open` twice gives them back, for each of the bits that move, on their own and with others. -/
theorem openFlags_involutive : ∀ flags ∈ (List.range 16).map (fun bits => 0o102 + (bits &&& 3) * 0x4000 + (bits / 4) * 0x10000),
    Architecture.aarch64.openFlags (Architecture.aarch64.openFlags flags) = flags := by decide +kernel

/-- `O_DIRECTORY` of AArch64 is what the kernel calls so. -/
theorem openFlags_directory : Architecture.aarch64.openFlags 0x4000 = Kernel.oDirectory := by decide +kernel

/-- `O_NOFOLLOW` of AArch64 is what the kernel calls so. -/
theorem openFlags_nofollow : Architecture.aarch64.openFlags 0x8000 = Kernel.oNofollow := by decide +kernel

/-- A file has what was written where it was written, and no less than it had. -/
theorem writeAt_size (data : ByteArray) (offset : Nat) (bytes : ByteArray) (h : offset ≤ data.size) :
    (writeAt data offset bytes).size = max data.size (offset + bytes.size) := by
  have hnot : ¬ data.size < offset := by omega
  simp only [writeAt, hnot, ↓reduceIte, ByteArray.size_append, ByteArray.size_extract]
  omega

/-- What is not an ELF file doesn't start. -/
theorem parse_short (data : ByteArray) (h : data.size < 52) : ∃ error, Elf.parse data = .error error := by
  refine ⟨"not an ELF file", ?_⟩
  simp [Elf.parse, h, bind, Except.bind]

/-! ### What a checkpoint holds of a kernel comes back -/

namespace Wire

/-- `data` starts with `head`. -/
def Prefix (head data : ByteArray) : Prop := ∃ rest, data = head ++ rest

theorem Prefix.refl (data : ByteArray) : Prefix data data :=
  ⟨ByteArray.empty, by simp⟩

theorem Prefix.trans {a b c : ByteArray} : Prefix a b → Prefix b c → Prefix a c := by
  rintro ⟨r, rfl⟩ ⟨s, rfl⟩
  exact ⟨r ++ s, by simp [ByteArray.append_assoc]⟩

theorem Prefix.size_le {a b : ByteArray} : Prefix a b → a.size ≤ b.size := by
  rintro ⟨r, rfl⟩
  simp [ByteArray.size_append]

theorem Prefix.getElem {a b : ByteArray} (h : Prefix a b) {i : Nat} (hi : i < a.size) :
    b[i]'(Nat.lt_of_lt_of_le hi h.size_le) = a[i] := by
  obtain ⟨r, rfl⟩ := h
  simp [ByteArray.getElem_append_left hi]

theorem prefix_push (out : ByteArray) (byte : UInt8) : Prefix out (out.push byte) :=
  ⟨ByteArray.mk #[byte], by ext1; simp⟩

private theorem getElem_pushed (out : ByteArray) (byte : UInt8) :
    (out.push byte)[out.size]'(by simp) = byte := by
  exact Array.getElem_push_eq

private theorem toNat_toUInt8_of_lt {value : Nat} (h : value < 256) : value.toUInt8.toNat = value := by
  show (UInt8.ofNat value).toNat = value
  rw [UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

private theorem scale_split (a b s : Nat) : (a + 128 * b) * s = a * s + b * (s * 128) := by
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm 128 s]

theorem prefix_append (out tail : ByteArray) : Prefix out (out ++ tail) := ⟨tail, rfl⟩

/-- An encoder only adds to what it is given. -/
def Extends (put : ByteArray → α → ByteArray) : Prop := ∀ out x, Prefix out (put out x)

/-- A decoder at the offset where an encoder started reads what it wrote, and stops where it stopped, whatever comes after. -/
def Inverts (put : ByteArray → α → ByteArray) (get : Decoder α) : Prop :=
  ∀ data out x, Prefix (put out x) data → get data out.size = .ok (x, (put out x).size)

theorem putNat_extends : Extends putNat := by
  intro out value
  induction value using Nat.strongRecOn generalizing out with
  | _ value ih =>
    rw [putNat]
    split
    · exact prefix_push _ _
    · exact (prefix_push _ _).trans (ih _ (by omega) _)

private theorem getNatFrom_putNat (value : Nat) :
    ∀ (data out : ByteArray) (scale acc fuel : Nat), Prefix (putNat out value) data →
      (putNat out value).size - out.size ≤ fuel →
      getNatFrom data fuel out.size scale acc = .ok (acc + value * scale, (putNat out value).size) := by
  induction value using Nat.strongRecOn with
  | _ value ih =>
    intro data out scale acc fuel hp hf
    have hpush : ∀ byte : UInt8, (out.push byte).size = out.size + 1 := by simp
    rw [putNat] at hp hf ⊢
    split at hp <;> rename_i hsmall
    · simp only [hsmall, ↓reduceIte] at hf ⊢
      rw [hpush] at hf ⊢
      have hbig := hp.size_le
      rw [hpush] at hbig
      have hat : out.size < data.size := by omega
      obtain ⟨fuel, rfl⟩ : ∃ next, fuel = next + 1 := ⟨fuel - 1, by omega⟩
      have hbyte : data[out.size].toNat = value := by
        have h := hp.getElem (i := out.size) (by rw [hpush]; omega)
        rw [h, getElem_pushed]
        exact toNat_toUInt8_of_lt (by omega)
      simp [getNatFrom, hat, hbyte, hsmall]
    · simp only [hsmall, ↓reduceIte] at hf ⊢
      have hnext := putNat_extends (out.push ((value % 128 + 128).toUInt8)) (value / 128)
      have hsize := hnext.size_le
      rw [hpush] at hsize
      have hbig := hp.size_le
      have hat : out.size < data.size := by omega
      obtain ⟨fuel, rfl⟩ : ∃ next, fuel = next + 1 := by
        refine ⟨fuel - 1, ?_⟩
        omega
      have hmod : value % 128 + 128 < 256 := by omega
      have hbyte : data[out.size].toNat = value % 128 + 128 := by
        have h := (hnext.trans hp).getElem (i := out.size) (by rw [hpush]; omega)
        rw [h, getElem_pushed]
        exact toNat_toUInt8_of_lt hmod
      have hrec := ih (value / 128) (by omega) data (out.push ((value % 128 + 128).toUInt8)) (scale * 128)
        (acc + (value % 128 + 128 - 128) * scale) fuel hp (by rw [hpush]; omega)
      rw [hpush] at hrec
      simp only [getNatFrom, hat, ↓reduceDIte, hbyte]
      rw [ite_eq_right (by omega), hrec]
      have hdrop : value % 128 + 128 - 128 = value % 128 := by omega
      have hsum : acc + (value % 128) * scale + (value / 128) * (scale * 128) = acc + value * scale := by
        rw [Nat.add_assoc, ← scale_split, Nat.mod_add_div]
      rw [hdrop, hsum]

theorem putNat_inverts : Inverts putNat getNat := by
  intro data out value hp
  refine getNatFrom_putNat value data out 1 0 _ hp ?_ |>.trans ?_
  · have := hp.size_le
    omega
  · simp

theorem putBytes_extends : Extends putBytes :=
  fun out data => (putNat_extends out data.size).trans (prefix_append _ _)

theorem putBytes_inverts : Inverts putBytes getBytes := by
  rintro data out bytes ⟨rest, rfl⟩
  unfold putBytes getBytes
  have hnat := putNat_inverts (putNat out bytes.size ++ bytes ++ rest) out bytes.size ⟨bytes ++ rest, by rw [ByteArray.append_assoc]⟩
  simp only [hnat, bind, Except.bind]
  have hsize : (putNat out bytes.size).size + bytes.size = (putNat out bytes.size ++ bytes).size := by
    simp [ByteArray.size_append]
  rw [ite_eq_left (by simp [ByteArray.size_append]), hsize, ByteArray.extract_append_size_left,
    ByteArray.extract_append_eq_right rfl (by simp [ByteArray.size_append])]

theorem putText_extends : Extends putText := fun out text => putBytes_extends out text.toUTF8

private theorem fromUTF8_toByteArray (text : String) : String.fromUTF8? text.toByteArray = some text := by
  unfold String.fromUTF8?
  rw [dite_eq_left text.isValidUTF8]
  rfl

theorem putText_inverts : Inverts putText getText := by
  intro data out text hp
  have h := putBytes_inverts data out text.toUTF8 hp
  simp [getText, h, bind, Except.bind, putText, fromUTF8_toByteArray]

theorem putList_extends {put : ByteArray → α → ByteArray} (h : Extends put) : Extends (putList put) := by
  intro out items
  have hfold : ∀ (items : List α) (out : ByteArray), Prefix out (items.foldl put out) := by
    intro items
    induction items with
    | nil => intro out; exact Prefix.refl _
    | cons x rest ih => intro out; exact (h out x).trans (ih _)
  exact (putNat_extends out items.length).trans (hfold _ _)

theorem putList_inverts {put : ByteArray → α → ByteArray} {get : Decoder α} (he : Extends put) (hi : Inverts put get) :
    Inverts (putList put) (getList get) := by
  intro data out items hp
  have hfold : ∀ (items : List α) (out : ByteArray), Prefix out (items.foldl put out) := by
    intro items
    induction items with
    | nil => intro out; exact Prefix.refl _
    | cons x rest ih => intro out; exact (he out x).trans (ih _)
  have hitems : ∀ (items : List α) (out : ByteArray) (seen : List α), Prefix (items.foldl put out) data →
      getItems get data items.length out.size seen = .ok (seen.reverse ++ items, (items.foldl put out).size) := by
    intro items
    induction items with
    | nil => intro out seen _; simp [getItems]
    | cons x rest ih =>
      intro out seen hp
      have hone := hi data out x ((hfold rest _).trans hp)
      simp only [List.length_cons, getItems, hone, bind, Except.bind]
      simpa using ih (put out x) (x :: seen) hp
  have hcount := putNat_inverts data out items.length ((hfold items _).trans hp)
  simp only [getList, hcount, bind, Except.bind]
  simpa [putList] using hitems items (putNat out items.length) [] hp

end Wire

namespace Image

open Wire

theorem putBool_extends : Extends putBool := fun out _ => putNat_extends out _

theorem putBool_inverts : Inverts putBool getBool := by
  intro data out value hp
  have h := putNat_inverts data out (if value then 1 else 0) hp
  cases value <;> simp_all [getBool, putBool, bind, Except.bind]

theorem putDescriptor_extends : Extends putDescriptor := fun out _ =>
  (putNat_extends out _).trans ((putNat_extends _ _).trans (putBool_extends _ _))

theorem putDescriptor_inverts : Inverts putDescriptor getDescriptor := by
  rintro data out ⟨fd, openFile, closeOnExec⟩ hp
  have h3 := putBool_inverts data _ closeOnExec hp
  have h2 := putNat_inverts data _ openFile ((putBool_extends _ closeOnExec).trans hp)
  have h1 := putNat_inverts data out fd ((putNat_extends _ openFile).trans ((putBool_extends _ closeOnExec).trans hp))
  simp [getDescriptor, putDescriptor, h1, h2, h3, bind, Except.bind]

theorem putPath_extends : Extends putPath := fun out _ => (putText_extends out _).trans (putNat_extends _ _)

theorem putPath_inverts : Inverts putPath getPath := by
  rintro data out ⟨path, inode⟩ hp
  have h2 := putNat_inverts data _ inode hp
  have h1 := putText_inverts data out path ((putNat_extends _ inode).trans hp)
  simp [getPath, putPath, h1, h2, bind, Except.bind]

theorem putOpenFile_extends : Extends putOpenFile := fun out _ =>
  (putNat_extends out _).trans ((putNat_extends _ _).trans ((putNat_extends _ _).trans (putNat_extends _ _)))

theorem putOpenFile_inverts : Inverts putOpenFile getOpenFile := by
  rintro data out ⟨id, inode, offset, flags⟩ hp
  have h4 := putNat_inverts data _ flags hp
  have p3 := (putNat_extends _ flags).trans hp
  have h3 := putNat_inverts data _ offset p3
  have p2 := (putNat_extends _ offset).trans p3
  have h2 := putNat_inverts data _ inode p2
  have h1 := putNat_inverts data out id ((putNat_extends _ inode).trans p2)
  simp [getOpenFile, putOpenFile, h1, h2, h3, h4, bind, Except.bind]

theorem putInode_extends : Extends putInode := fun out _ =>
  (putNat_extends out _).trans ((putNat_extends _ _).trans ((putNat_extends _ _).trans (putBytes_extends _ _)))

theorem putInode_inverts : Inverts putInode getInode := by
  rintro data out ⟨number, mode, kind, bytes⟩ hp
  have h4 := putBytes_inverts data _ bytes hp
  have p3 := (putBytes_extends _ bytes).trans hp
  have h3 := putNat_inverts data _ kind p3
  have p2 := (putNat_extends _ kind).trans p3
  have h2 := putNat_inverts data _ mode p2
  have h1 := putNat_inverts data out number ((putNat_extends _ mode).trans p2)
  simp [getInode, putInode, h1, h2, h3, h4, bind, Except.bind]

theorem putProcess_extends : Extends putProcess := fun out _ =>
  (putNat_extends out _).trans ((putList_extends putDescriptor_extends _ _).trans ((putText_extends _ _).trans
    ((putNat_extends _ _).trans ((putNat_extends _ _).trans (putNat_extends _ _)))))

theorem putProcess_inverts : Inverts putProcess getProcess := by
  rintro data out ⟨group, descriptors, cwd, umask, breakStart, breakEnd⟩ hp
  have h6 := putNat_inverts data _ breakEnd hp
  have p5 := (putNat_extends _ breakEnd).trans hp
  have h5 := putNat_inverts data _ breakStart p5
  have p4 := (putNat_extends _ breakStart).trans p5
  have h4 := putNat_inverts data _ umask p4
  have p3 := (putNat_extends _ umask).trans p4
  have h3 := putText_inverts data _ cwd p3
  have p2 := (putText_extends _ cwd).trans p3
  have h2 := putList_inverts putDescriptor_extends putDescriptor_inverts data _ descriptors p2
  have h1 := putNat_inverts data out group ((putList_extends putDescriptor_extends _ descriptors).trans p2)
  simp [getProcess, putProcess, h1, h2, h3, h4, h5, h6, bind, Except.bind]

/-- A checkpoint reads back as the image that it was made from, wherever in a file that is and whatever comes after it. -/
theorem decode_encode (data out : ByteArray) (image : Image) (hp : Prefix (encode out image) data) :
    decode data out.size = .ok (image, (encode out image).size) := by
  obtain ⟨paths, inodes, nextInode, openFiles, nextOpenFile, processes, output, clock, cycles⟩ := image
  have h9 := putNat_inverts data _ cycles hp
  have p8 := (putNat_extends _ cycles).trans hp
  have h8 := putNat_inverts data _ clock p8
  have p7 := (putNat_extends _ clock).trans p8
  have h7 := putBytes_inverts data _ output p7
  have p6 := (putBytes_extends _ output).trans p7
  have h6 := putList_inverts putProcess_extends putProcess_inverts data _ processes p6
  have p5 := (putList_extends putProcess_extends _ processes).trans p6
  have h5 := putNat_inverts data _ nextOpenFile p5
  have p4 := (putNat_extends _ nextOpenFile).trans p5
  have h4 := putList_inverts putOpenFile_extends putOpenFile_inverts data _ openFiles p4
  have p3 := (putList_extends putOpenFile_extends _ openFiles).trans p4
  have h3 := putNat_inverts data _ nextInode p3
  have p2 := (putNat_extends _ nextInode).trans p3
  have h2 := putList_inverts putInode_extends putInode_inverts data _ inodes p2
  have p1 := (putList_extends putInode_extends _ inodes).trans p2
  have h1 := putList_inverts putPath_extends putPath_inverts data out paths p1
  simp [decode, encode, h1, h2, h3, h4, h5, h6, h7, h8, h9, bind, Except.bind]

/-- What comes after the image in a file is where the emulator starts: nothing of one reads into the other. -/
theorem decode_encode_append (out : ByteArray) (image : Image) (rest : ByteArray) :
    decode (encode out image ++ rest) out.size = .ok (image, (encode out image).size) :=
  decode_encode _ out image ⟨rest, rfl⟩

end Image

end Bap.Linux
