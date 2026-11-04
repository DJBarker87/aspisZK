import NGD_DecodeEntry
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_CheckedOps
theorem mul (x y z : Usize) (equation : x.val*y.val=z.val) :
    Usize.checked_mul x y=some z := by
  have bounded : x.val*y.val≤Usize.max := by rw [equation];have h:=z.hmax;scalar_tac
  obtain ⟨value,run,eq⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y) bounded)
  have same : value=z := UScalar.eq_of_val_eq (eq.trans equation)
  simp [Usize.checked_mul,core.num.checked_mul_UScalar,run,same]

theorem add (x y z : Usize) (equation : x.val+y.val=z.val) :
    Usize.checked_add x y=some z := by
  have bounded : x.val+y.val≤Usize.max := by rw [equation];have h:=z.hmax;scalar_tac
  obtain ⟨value,run,eq⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) bounded)
  have same : value=z := UScalar.eq_of_val_eq (eq.trans equation)
  simp [Usize.checked_add,core.num.checked_add_UScalar,run,same]
#print axioms mul
#print axioms add
end NGO_CheckedOps
