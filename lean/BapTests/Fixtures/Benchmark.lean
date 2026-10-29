import Bap

private def sum (n : Nat) (acc : UInt64) : UInt64 :=
  match n with
  | 0 => acc
  | n + 1 => sum n (acc + UInt64.ofNat (n + 1))

def main : IO Unit := do
  IO.println s!"{sum 10000000 0}"
