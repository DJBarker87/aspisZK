import PV_L2E_DigitsTrace
import PV_L2E_WordRank
import PV_L2E_CarryValue
set_option autoImplicit false
namespace PV_L2E_DigitsValue
open PV_L2D_DivisionBounds PV_L2E_DigitsTrace

/-- Whole-array reconstruction of n successive divisions. -/
theorem reconstruct (n : Nat) (xs : List Nat) :
    PV_L2E_WordRank.rank (run n xs).quotient*P^n +
      PV_L2E_CarryValue.value (run n xs).digits=PV_L2E_WordRank.rank xs := by
  induction n generalizing xs with
  | zero => simp [run,PV_L2E_CarryValue.value]
  | succ n ih =>
    have hp := PV_L2E_WordRank.reconstruct 0 xs
    have ht := ih (pass 0 xs).1
    simp only [Nat.zero_mul,zero_add] at hp
    simp only [run,PV_L2E_DivisionTrace.complete_value,
      PV_L2E_CarryValue.value,pow_succ]
    linear_combination hp + P*ht

/-- The emitted digits are exactly the canonical residue, not just bounded
words or an assumed successful decoder. -/
theorem residue (n : Nat) (xs : List Nat) (hx : ∀ x∈xs,x<B) :
    PV_L2E_CarryValue.value (run n xs).digits=PV_L2E_WordRank.rank xs % P^n := by
  have h := reconstruct n xs
  have hb := PV_L2E_CarryValue.value_bound (run n xs).digits (bounds n xs hx).2
  rw [digit_count] at hb
  rw [←h,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_eq_of_lt hb]

/-- The high quotient bound consumed by gamma's q+1 and second-wrap proof. -/
theorem quotient_256 (xs : List Nat) (width : xs.length=8)
    (hx : ∀ x∈xs,x<B) : PV_L2E_WordRank.rank (run 8 xs).quotient≤256 := by
  have h := reconstruct 8 xs
  have hb := PV_L2E_WordRank.bound xs hx
  rw [width] at hb
  have hc : B^8<257*P^8 := by norm_num [B,P]
  have hp : 0<P^8 := pow_pos (by decide : 0<P) _
  nlinarith

#print axioms reconstruct
#print axioms residue
#print axioms quotient_256
end PV_L2E_DigitsValue
