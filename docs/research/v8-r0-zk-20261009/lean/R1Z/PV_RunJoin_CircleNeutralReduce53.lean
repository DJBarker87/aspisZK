import R1Z.PV_RunJoin_CircleNeutralFold53
import R1Z.PV_RunJoin_CircleNeutralSubtract53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralReduce53
open PV_RunJoin_CircleNeutralFold53 PV_RunJoin_CircleNeutralShape53

def word (x : U64) : U32 := UScalar.cast .U32 (fold (fold x))

theorem word_val (x : U64) : (word x).val = (fold (fold x)).val := by
  have hb := fold_twice_bound x
  change ((fold (fold x)).bv.setWidth 32).toNat = (fold (fold x)).val
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by change (fold (fold x)).val < 4294967296;omega)

theorem source (x : U64) : PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x =
    PV_RunJoin_CircleRawScalar52.field.ct.subtract_p (word x) := by
  unfold PV_RunJoin_CircleRawScalar52.field.ct.reduce64
  simp only [lift,bind_tc_ok]
  rfl

theorem total (x : U64) : ∃ y,
    PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x = ok y ∧ Canon y := by
  rw [source]
  apply PV_RunJoin_CircleNeutralSubtract53.total
  rw [word_val]
  exact fold_twice_bound x

#print axioms word
#print axioms word_val
#print axioms source
#print axioms total
end R1Z.PV_RunJoin_CircleNeutralReduce53
