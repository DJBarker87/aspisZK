import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace LPe_MersenneReduction
/-- Natural-number counterpart of each 31-bit fold in canonical::reduce.
The Rust word-to-natural refinement is a separate source boundary. -/
def fold (n : Nat) : Nat := n % 2147483648 + n / 2147483648
def reduce (n : Nat) : Nat :=
  let m := fold (fold n)
  if m ≥ 2147483647 then m - 2147483647 else m

theorem fold_mod (n : Nat) : fold n % 2147483647 = n % 2147483647 := by
  have h := congrArg (fun x : Nat => x % 2147483647)
    (Nat.mod_add_div n 2147483648)
  have hb : 2147483648 % 2147483647 = 1 := by decide
  simpa only [fold, Nat.add_mod, Nat.mul_mod, hb, Nat.one_mul, Nat.mod_mod] using h

theorem fold_twice_lt (n : Nat) (hn : n < 18446744073709551616) :
    fold (fold n) < 4294967294 := by
  dsimp [fold]
  omega

/-- Exact Mersenne residue for all u64-sized natural inputs, without
normalizing any concrete multiplication or recurrence cell. -/
theorem reduce_eq_mod (n : Nat) (hn : n < 18446744073709551616) :
    reduce n = n % 2147483647 := by
  have hlt := fold_twice_lt n hn
  have hmod : fold (fold n) % 2147483647 = n % 2147483647 := by
    rw [fold_mod, fold_mod]
  dsimp only [reduce]
  split_ifs with h
  · omega
  · omega

theorem zero_witness : reduce 0 = 0 := by decide
#print axioms fold_mod
#print axioms fold_twice_lt
#print axioms reduce_eq_mod
#print axioms zero_witness
end LPe_MersenneReduction
