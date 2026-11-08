import NNU_OffsetArithmetic
set_option autoImplicit false
namespace AspisR1.NNU_OffsetSubtract
open Aeneas Aeneas.Std Result

theorem sub (x y z : Usize) (bound : y.val≤x.val) (value : x.val-y.val=z.val) : (x-y : Result Usize) = .ok z := by
 obtain ⟨out,run,values⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=x) (y:=y) (by scalar_tac))
 have same : out=z := UScalar.eq_of_val_eq (values.1.trans value)
 exact run.trans (congrArg Result.ok same)
#print axioms sub
end AspisR1.NNU_OffsetSubtract
