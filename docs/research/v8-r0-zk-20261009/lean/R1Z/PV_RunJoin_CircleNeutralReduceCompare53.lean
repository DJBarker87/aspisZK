import R1Z.PV_RunJoin_CircleNeutralReduce53
import R1Z.PV_RunJoin_CircleNeutralShift53
import R1Z.PV_RunJoin_CircleNeutralChecked64_53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralReduceCompare53
open PV_RunJoin_CircleNeutralFold53 PV_RunJoin_CircleNeutralShift53

theorem complete (x : U64) : PV_RunJoin_CircleR72Raw52.field.reduce_u64 x =
    PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x := by
  unfold PV_RunJoin_CircleR72Raw52.field.reduce_u64
  simp only [lift,bind_tc_ok,low_mask,shr31u]
  rw [PV_RunJoin_CircleNeutralChecked64_53.add _ _ (fold_no_overflow x)]
  simp only [bind_tc_ok]
  change (do
    let hi ← fold x >>> 31#u32
    let z ← low (fold x) + hi
    if UScalar.cast .U32 z ≥ PV_RunJoin_CircleR72Raw52.field.P
    then UScalar.cast .U32 z - PV_RunJoin_CircleR72Raw52.field.P
    else ok (UScalar.cast .U32 z)) = _
  rw [shr31u,bind_tc_ok,
    PV_RunJoin_CircleNeutralChecked64_53.add _ _ (fold_no_overflow (fold x)),bind_tc_ok,
    PV_RunJoin_CircleNeutralReduce53.source,PV_RunJoin_CircleNeutralSubtract53.source]
  change (if PV_RunJoin_CircleNeutralReduce53.word x ≥ 2147483647#u32
    then PV_RunJoin_CircleNeutralReduce53.word x - 2147483647#u32
    else ok (PV_RunJoin_CircleNeutralReduce53.word x)) = _
  unfold PV_RunJoin_CircleNeutralSubtract53.output
  split
  · exact PV_RunJoin_CircleNeutralScalar52.checked_sub _ _ (by assumption)
  · rfl

theorem total (x : U64) : ∃ y,
    PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x = ok y ∧
    PV_RunJoin_CircleR72Raw52.field.reduce_u64 x = ok y ∧
    PV_RunJoin_CircleNeutralShape53.Canon y := by
  obtain ⟨y,hy,hc⟩ := PV_RunJoin_CircleNeutralReduce53.total x
  exact ⟨y,hy,(complete x).trans hy,hc⟩

#print axioms complete
#print axioms total
end R1Z.PV_RunJoin_CircleNeutralReduceCompare53
