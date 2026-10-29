import R1SamplerNatModel
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
namespace R1Z.PV_RunJoin_DigitsValue50
open scoped BigOperators

theorem complete (p n : Nat) (f : Fin n → Nat) :
    AspisR1.SamplerAddDigits.digitsValue p (List.ofFn f)=∑ i : Fin n,f i*p^i.val := by
  induction n with
  | zero => simp only [List.ofFn_zero,AspisR1.SamplerAddDigits.digitsValue,Fin.sum_univ_zero]
  | succ n ih =>
    rw [List.ofFn_succ,AspisR1.SamplerAddDigits.digitsValue,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,pow_zero,Nat.mul_one,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
#print axioms complete
end R1Z.PV_RunJoin_DigitsValue50
