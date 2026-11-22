/-! Bytes of zeros, of the size of a mapping. Going through an array of them takes eight times the memory, and it is what a program
that maps its stacks spends most of its system time on. -/

namespace Bap

/-- `size` zeros. -/
def zeroBytes (size : Nat) : ByteArray := ByteArray.mk (Array.replicate size 0)

/-- `bytes` and `extra` zeros after them, as a region of a file that has less than it takes is. -/
def padZeros (bytes : ByteArray) (extra : Nat) : ByteArray := bytes.append (zeroBytes extra)

/-- `chunk` after `bytes`, `count` times. -/
private def appendChunks (bytes chunk : ByteArray) : Nat → ByteArray
  | 0 => bytes
  | count + 1 => appendChunks (bytes ++ chunk) chunk count

/-- What `padZeros` is, in memory of the size of what it makes and no more: room for all of it first, which the bytes and then a page
of zeros at a time are put in, rather than zeros of their own that are then copied after the bytes. -/
def padZerosFast (bytes : ByteArray) (extra : Nat) : ByteArray :=
  if extra ≤ 4096 then bytes.append (ByteArray.mk (Array.replicate extra 0))
  else
    let page := ByteArray.mk (Array.replicate 4096 0)
    appendChunks (ByteArray.emptyWithCapacity (bytes.size + extra) ++ bytes) page (extra / 4096) ++ page.extract 0 (extra % 4096)

private theorem appendChunks_zeros (size : Nat) : ∀ (count : Nat) (bytes : ByteArray),
    appendChunks bytes (ByteArray.mk (Array.replicate size 0)) count = bytes ++ ByteArray.mk (Array.replicate (count * size) 0)
  | 0, bytes => by
    apply ByteArray.ext
    simp [appendChunks]
  | count + 1, bytes => by
    rw [appendChunks, appendChunks_zeros size count]
    apply ByteArray.ext
    simp only [ByteArray.data_append, Array.append_assoc, Array.replicate_append_replicate]
    congr 2
    rw [Nat.succ_mul, Nat.add_comm]

private theorem padZerosFast_eq (bytes : ByteArray) (extra : Nat) : padZerosFast bytes extra = padZeros bytes extra := by
  rw [padZerosFast]
  split
  · rfl
  · simp only []
    rw [appendChunks_zeros]
    apply ByteArray.ext
    show _ = (bytes ++ zeroBytes extra).data
    simp only [zeroBytes, ByteArray.data_extract, ByteArray.data_append, Array.append_assoc, Array.extract_replicate,
      Array.replicate_append_replicate, ByteArray.emptyWithCapacity]
    refine Array.empty_append.trans ?_
    congr 2
    omega

@[csimp] theorem padZeros_eq_fast : @padZeros = @padZerosFast := by
  funext bytes extra
  exact (padZerosFast_eq bytes extra).symm

/-- What `zeroBytes` is: zeros after no bytes, in memory of their size. -/
def zeroBytesFast (size : Nat) : ByteArray := padZerosFast ByteArray.empty size

@[csimp] theorem zeroBytes_eq_fast : @zeroBytes = @zeroBytesFast := by
  funext size
  rw [zeroBytesFast, padZerosFast_eq]
  apply ByteArray.ext
  show _ = (ByteArray.empty ++ zeroBytes size).data
  simp

@[simp] theorem zeroBytes_size (size : Nat) : (zeroBytes size).size = size := by
  simp [zeroBytes, ByteArray.size]

@[simp] theorem padZeros_size (bytes : ByteArray) (extra : Nat) : (padZeros bytes extra).size = bytes.size + extra := by
  show (bytes ++ zeroBytes extra).size = _
  simp

end Bap
