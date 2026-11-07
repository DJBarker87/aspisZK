import NMP_DirectBind
set_option autoImplicit false
namespace AspisR1.NMP_UsizeExact
open Aeneas Aeneas.Std Result
theorem mul (x y z : Usize) (h : x.val*y.val=z.val) : (x*y : Result Usize) = ok z := by
 obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y) (by scalar_tac))
 have same : r=z := UScalar.eq_of_val_eq (hv.trans h)
 simpa only [same] using hr
theorem add (x y z : Usize) (h : x.val+y.val=z.val) : (x+y : Result Usize) = ok z := by
 obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
 have same : r=z := UScalar.eq_of_val_eq (hv.trans h)
 simpa only [same] using hr
theorem sub (x y z : Usize) (lo : y.val≤x.val) (h : x.val-y.val=z.val) : (x-y : Result Usize) = ok z := by
 obtain ⟨r,hr,hv⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=x) (y:=y) (by scalar_tac))
 have same : r=z := UScalar.eq_of_val_eq (hv.1.trans h)
 simpa only [same] using hr
theorem wrapping_add (x y z : Usize) (h : x.val+y.val=z.val) : Usize.wrapping_add x y=z := by
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_add_val_eq,h]
 apply Nat.mod_eq_of_lt
 simpa only [UScalar.size_def] using z.hmax
#print axioms mul
#print axioms add
#print axioms sub
#print axioms wrapping_add
end AspisR1.NMP_UsizeExact
