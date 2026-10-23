import AdapterRwModel
set_option autoImplicit false
namespace AspisR1.AdapterRw.Scalar
open Aeneas Aeneas.Std Result

theorem add_eq (x y z : Usize) (value : x.val + y.val = z.val) : x + y = ok z := by
  obtain ⟨out,run,exactValue⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := x) (y := y) (by rw [value]; scalar_tac))
  have same : out = z := UScalar.eq_of_val_eq (exactValue.trans value)
  simpa only [same] using run

theorem mul_eq (x y z : Usize) (value : x.val * y.val = z.val) : x * y = ok z := by
  obtain ⟨out,run,exactValue⟩ := WP.spec_imp_exists
    (UScalar.mul_spec (x := x) (y := y) (by rw [value]; scalar_tac))
  have same : out = z := UScalar.eq_of_val_eq (exactValue.trans value)
  simpa only [same] using run

theorem sub_eq (x y z : Usize) (within : y.val ≤ x.val)
    (value : x.val - y.val = z.val) : x - y = ok z := by
  obtain ⟨out,run,exactValue,_⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := x) (y := y) within)
  have same : out = z := UScalar.eq_of_val_eq (exactValue.trans value)
  simpa only [same] using run

theorem checked_add_eq (x y z : Usize) (value : x.val + y.val = z.val) :
    Usize.checked_add x y = some z := by
  change Option.ofResult (x + y) = some z
  rw [add_eq x y z value]
  rfl

#print axioms checked_add_eq
#print axioms add_eq
#print axioms mul_eq
#print axioms sub_eq
end AspisR1.AdapterRw.Scalar
