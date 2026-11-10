-- Gate model definitions copied verbatim (Nat-only part) from
-- terminal-v4-funs-external-countones-v5-20261019/source.lean and the FIq_NativeExternal trailing_zeros_aux.
def count_ones_aux (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if Nat.testBit n k then 1 else 0) + count_ones_aux n k
def trailing_zeros_aux (n : Nat) : Nat → Nat
  | 0 => 16
  | k + 1 => if Nat.testBit n k then min k (trailing_zeros_aux n k)
             else trailing_zeros_aux n k
def fold : Nat → Nat → Nat → Nat
  | 0, acc, _ => acc
  | m+1, acc, x =>
    let v := count_ones_aux x 16 * 32 + trailing_zeros_aux x 16
    fold m ((acc * 1000003 + v) % 18446744073709551616) (x+1)
#eval fold 65536 0 0
