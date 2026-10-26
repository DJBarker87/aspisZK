import JFv_Value
set_option autoImplicit false
namespace AspisR1.JFv_Checked
open Aeneas Aeneas.Std Result WP

theorem multiply (x y : Usize) (bound : x.val*y.val ≤ Usize.max) :
    ∃ value,Usize.checked_mul x y=some value ∧ value.val=x.val*y.val := by
  have h : (x*y : Result Usize) ⦃ value => value.val=x.val*y.val ⦄ := by step* <;> scalar_tac
  obtain ⟨value,call,numeric⟩ := WP.spec_imp_exists h
  refine ⟨value,?_,numeric⟩
  unfold Usize.checked_mul core.num.checked_mul_UScalar
  rw [call]
  rfl

theorem add (x y : Usize) (bound : x.val+y.val ≤ Usize.max) :
    ∃ value,Usize.checked_add x y=some value ∧ value.val=x.val+y.val := by
  have h : (x+y : Result Usize) ⦃ value => value.val=x.val+y.val ⦄ := by step* <;> scalar_tac
  obtain ⟨value,call,numeric⟩ := WP.spec_imp_exists h
  refine ⟨value,?_,numeric⟩
  unfold Usize.checked_add core.num.checked_add_UScalar
  rw [call]
  rfl

#print axioms multiply
#print axioms add
end AspisR1.JFv_Checked
