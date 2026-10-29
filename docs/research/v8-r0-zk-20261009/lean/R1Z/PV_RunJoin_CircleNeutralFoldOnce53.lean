import R1Z.PV_RunJoin_CircleNeutralReduce53
import R1Z.PV_RunJoin_CircleNeutralCast53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralFoldOnce53
open PV_RunJoin_CircleNeutralFold53 PV_RunJoin_CircleNeutralCast53

theorem stable (s : U64) (hs : s.val < 4294967294) :
    PV_RunJoin_CircleNeutralSubtract53.output (UScalar.cast .U32 (fold s)) =
      PV_RunJoin_CircleNeutralSubtract53.output (UScalar.cast .U32 s) := by
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_CircleNeutralSubtract53.value,PV_RunJoin_CircleNeutralSubtract53.value]
  have hf : (fold s).val < 4294967296 := by rw [fold_val];omega
  rw [down_val (fold s) hf,down_val s (by omega),fold_val]
  split <;> split <;> omega

theorem product_fold_bound (x : U64) (hx : x.val < 4611686014132420609) :
    (fold x).val < 4294967294 := by
  rw [fold_val]
  omega

theorem source (x : U64) (hx : x.val < 4611686014132420609) :
    PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x =
      ok (PV_RunJoin_CircleNeutralSubtract53.output (UScalar.cast .U32 (fold x))) := by
  rw [PV_RunJoin_CircleNeutralReduce53.source,PV_RunJoin_CircleNeutralSubtract53.source]
  exact congrArg ok (stable (fold x) (product_fold_bound x hx))

#print axioms stable
#print axioms product_fold_bound
#print axioms source
end R1Z.PV_RunJoin_CircleNeutralFoldOnce53
