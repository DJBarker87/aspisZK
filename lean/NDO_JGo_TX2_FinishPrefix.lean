import JGo_TX2_FinishPrefixTools
import NDO_JFv_View
import NDO_JGo_TX2_NewWeights
import NDO_JGo_TX2_RoundCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_FinishPrefix
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish

def view (inactive : E) : verifier.View where
  variant := .S2
  semantic := JFv_View.emptySlice
  y1 := JFv_View.emptySlice
  inactive := inactive
  round0 := JFw_Frames.window 7527 224
  folded_root := none
  round1 := JFw_Frames.window 7783 224
  final_message := JFw_Frames.window 8007 2048
  query_bytes := JFv_View.emptySlice

def alphas : Slice E := ⟨[JFq_Alpha0.scalar,JFq_Alpha1.scalar],by simp;scalar_tac⟩

/-- The uncomputed Pair and dot gates remain in the actual returned computation.
The accumulator parameter can be instantiated ONLY with the query's return
and its actual flushed weight writeback in the joint call theorem. -/
theorem source (seed : FinishOps FIo_Install.W) (inactive : E) (a : verifier.Accumulator) :
    Port3_NativeFinishBody.verifier.finish_relation
      (Port4D_Round.native (FIo_Install.finishOps (.Ok ()) seed)) (view inactive) JFo_Prepared.value a none=
    JGo_TX2_FinishPrefixTools.remaining
      (Port4D_Round.native (FIo_Install.finishOps (.Ok ()) seed))
      (view inactive) JFo_Prepared.value a JGo_TX2_WeightData.value alphas JGo_TX2_Horner1_6.after := by
  apply JGo_TX2_FinishPrefixTools.source _ _ _ _
    JFq_Alpha0.scalar JFq_Alpha1.scalar JGo_TX2_Horner0_6.after JGo_TX2_Horner1_6.after
    JGo_TX2_WeightData.value alphas
  · rfl
  · exact JGo_TX2_RoundCalls.first seed
  · rfl
  · rfl
  · exact JGo_TX2_RoundCalls.second seed
  · exact JGo_TX2_NewWeights.source
  · rfl
#print axioms source
theorem installed (seed : FinishOps FIo_Install.W) (inactive : E) (a : verifier.Accumulator) :
    Port4D_FinishInstall.finish (FIo_Install.finishOps (.Ok ()) seed) (view inactive) JFo_Prepared.value a none=
      Port3_QueryInstall.result (JGo_TX2_FinishPrefixTools.remaining
        (Port4D_Round.native (FIo_Install.finishOps (.Ok ()) seed))
        (view inactive) JFo_Prepared.value a JGo_TX2_WeightData.value alphas JGo_TX2_Horner1_6.after) :=
  congrArg Port3_QueryInstall.result (source seed inactive a)
#print axioms installed
end AspisR1.JGo_TX2_FinishPrefix
end
