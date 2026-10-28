import NDO_JGm_TX2_View
set_option autoImplicit false
namespace AspisR1.JGm_TX2_Scalar
open Aeneas Aeneas.Std Result

theorem add (x y z : Usize) (sum : z.val=x.val+y.val) : x+y=ok z := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  have same : v=z := UScalar.eq_of_val_eq (by omega)
  simpa only [same] using run
#print axioms add

theorem sub (x y z : Usize) (order : y.val≤x.val) (diff : z.val=x.val-y.val) : x-y=ok z := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=x) (y:=y) (by scalar_tac))
  have same : v=z := UScalar.eq_of_val_eq (by omega)
  simpa only [same] using run
#print axioms sub
end AspisR1.JGm_TX2_Scalar
