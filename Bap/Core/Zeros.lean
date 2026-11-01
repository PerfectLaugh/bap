/-! Bytes of zeros, of the size of a mapping. Going through an array of them takes eight times the memory, and it is what a program
that maps its stacks spends most of its system time on. -/

namespace Bap

/-- `size` zeros. -/
def zeroBytes (size : Nat) : ByteArray := ByteArray.mk (Array.replicate size 0)

/-- What `zeroBytes` is: twice half as many, which is a copy of memory. -/
def zeroBytesFast (size : Nat) : ByteArray :=
  if size ≤ 4096 then ByteArray.mk (Array.replicate size 0)
  else
    let half := zeroBytesFast ((size + 1) / 2)
    (half ++ half).extract 0 size
termination_by size
decreasing_by omega

private theorem zeroBytesFast_eq (size : Nat) : zeroBytesFast size = zeroBytes size := by
  induction size using Nat.strongRecOn with
  | _ size ih =>
    rw [zeroBytesFast]
    split
    · rfl
    · rename_i hsize
      simp only
      rw [ih _ (by omega)]
      apply ByteArray.ext
      simp only [zeroBytes, ByteArray.data_extract, ByteArray.data_append, Array.replicate_append_replicate]
      rw [Array.extract_replicate]
      congr 1
      omega

@[csimp] theorem zeroBytes_eq_fast : @zeroBytes = @zeroBytesFast := by
  funext size
  exact (zeroBytesFast_eq size).symm

@[simp] theorem zeroBytes_size (size : Nat) : (zeroBytes size).size = size := by
  simp [zeroBytes, ByteArray.size]

end Bap
