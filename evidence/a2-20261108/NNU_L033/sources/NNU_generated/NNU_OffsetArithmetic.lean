import Aeneas
set_option autoImplicit false
namespace AspisR1.NNU_OffsetArithmetic
open Aeneas Aeneas.Std Result

theorem add (x y z : Usize) (value : x.val+y.val=z.val) : x+y=.ok z := by
 obtain ⟨out,run,values⟩ := WP.spec_imp_exists (UScalar.add_spec x y (by scalar_tac))
 have same : out=z := UScalar.eq_of_val_eq (values.trans value)
 exact run.trans (congrArg Result.ok same)

theorem mul (x y z : Usize) (value : x.val*y.val=z.val) : x*y=.ok z := by
 obtain ⟨out,run,values⟩ := WP.spec_imp_exists (UScalar.mul_spec x y (by scalar_tac))
 have same : out=z := UScalar.eq_of_val_eq (values.trans value)
 exact run.trans (congrArg Result.ok same)

theorem sub (x y z : Usize) (bound : y.val≤x.val) (value : x.val-y.val=z.val) : x-y=.ok z := by
 obtain ⟨out,run,values⟩ := WP.spec_imp_exists (UScalar.sub_spec x y (by scalar_tac))
 have same : out=z := UScalar.eq_of_val_eq (values.trans value)
 exact run.trans (congrArg Result.ok same)
#print axioms add
#print axioms mul
#print axioms sub
end AspisR1.NNU_OffsetArithmetic
