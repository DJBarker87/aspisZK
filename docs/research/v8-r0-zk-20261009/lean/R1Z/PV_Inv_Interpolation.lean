import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
set_option autoImplicit false
namespace R1Z.PV_Inv_Interpolation
open scoped BigOperators
variable {p n : ℕ} [Fact p.Prime]

theorem node_injective (hn : n ≤ p) : Function.Injective (fun i : Fin n => (i.val : ZMod p)) := by
  intro i j h
  apply Fin.ext
  have hi : i.val < p := lt_of_lt_of_le i.isLt hn
  have hj : j.val < p := lt_of_lt_of_le j.isLt hn
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] using hv

def denominator (n p : ℕ) (i : Fin n) : ZMod p :=
  ∏ j ∈ (Finset.univ.erase i), ((i.val : ZMod p) - (j.val : ZMod p))

theorem denominator_nonzero (hn : n ≤ p) (i : Fin n) : denominator n p i ≠ 0 := by
  unfold denominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 ((node_injective hn h).symm))

#print axioms node_injective
#print axioms denominator_nonzero
end R1Z.PV_Inv_Interpolation
