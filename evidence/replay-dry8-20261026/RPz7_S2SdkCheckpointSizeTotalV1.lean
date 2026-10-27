import S2SdkOwnedModelV1
import CurrentCallerUsizeArithmeticV1
import R22Stage2LeafTotal
import RPz7_Tx1FinalLenBoundV8
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.CheckpointSizeTotal

/-- Exact emitted constant identity; reuse the already checked symbolic
straight-line arithmetic instead of evaluating this definition again. -/
theorem fixed_eq : aspis_r1_cost_probe.verifier.CHECKPOINT_FIXED =
    AspisR1Stage2.verifier.CHECKPOINT_FIXED := by
  unfold aspis_r1_cost_probe.verifier.CHECKPOINT_FIXED AspisR1Stage2.verifier.CHECKPOINT_FIXED
  rfl

theorem fixed_total : aspis_r1_cost_probe.verifier.CHECKPOINT_FIXED=ok 744#usize := by
  rw [fixed_eq]
  exact AspisR1Stage2.r22_verifier_CHECKPOINT_FIXED_total

def retainedVariant : aspis_r1_cost_probe.transport.Variant → AspisR1PublicPreparation.transport.Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

/-- Complete helper identity, checked separately on the three source variants. -/
theorem final_len_eq (variant : aspis_r1_cost_probe.transport.Variant) :
    aspis_r1_cost_probe.transport.Variant.final_len variant =
      AspisR1PublicPreparation.Tx1Model.final_len (retainedVariant variant) := by
  cases variant <;> rfl

theorem final_len_S2 : aspis_r1_cost_probe.transport.Variant.final_len .S2=ok 64#usize := by
  rw [final_len_eq]
  exact Tx1FinalLenBoundV6.final_len_cases .S2

/-- TOTAL exact size used by the actual owned SDK checkpoint guard. -/
theorem checkpoint_size_S2 : aspis_r1_cost_probe.verifier.checkpoint_size .S2=ok 1768#usize := by
  have hm : (16#usize*64#usize : Result Usize)=ok 1024#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok <;> scalar_tac
  have ha : (744#usize+1024#usize : Result Usize)=ok 1768#usize := by
    apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
  simp only [aspis_r1_cost_probe.verifier.checkpoint_size,final_len_S2,hm,fixed_total,ha,bind_tc_ok]

#print axioms fixed_eq
#print axioms fixed_total
#print axioms final_len_eq
#print axioms final_len_S2
#print axioms checkpoint_size_S2
end AspisS2OwnedStage1.SdkReference.CheckpointSizeTotal
