import JGs_Regular
import JGs_Inactive
import JGs_LibraSource
import JGq_PairCalls
import FJr_BodyPairMeaning
import FJv_Top
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Calls
open Aeneas Aeneas.Std Result
/-- Constructed native calls on the actual retained operands. This does not
assert that the Pair parent or either accepted wrapper has returned. -/
def Facts : Prop :=
  @FIo_Native.weights.process_regular_kinds (FIo_Install.allocation (.Ok ()))
    JGq_PairShape.w true JGq_PairShape.alpha JGq_PairShape.f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 JGq_PairShape.scratch JGq_PairPrefix.initial=
      ok (.Ok (),JGs_K4.scratch,JGs_K4.parts) ∧
  FIo_Native.weights.grouped_inactive_pair JGq_PairShape.w JGq_PairShape.f JGq_Low.a16=ok JGs_Inactive.pair12 ∧
  FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra=ok JGs_LibraEnd.value

theorem source : Facts := ⟨JGs_Regular.source,JGs_Inactive.source,JGs_LibraSource.source⟩
#print axioms source

/-- The inherited SAME saved-byte reader/batch/query/flush fixture plus these
constructed calls. Oracle realization stays explicit; no Pair success assumed. -/
theorem on_saved (saved : alloc.vec.Vec U8) (same : saved.val=JFx_NativeBytes.checkpoint.val)
    {C Hash : Type} (base : VTop_Stages.Ops) (seed : AspisR1Stage2.Stage2Finish.FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    Port4A_ReaderInstall.reader true (JFn_HashBoundary.dictionary JFp_SHADigest.digest D)
      (⟨saved.val,saved.property⟩ : Slice U8) JFx_NativeBytes.proof JFx_NativeBytes.publicInput .S2 hash=
        ok (.Ok (JFo_Prepared.value,JFo_Prepared.accumulator)) ∧
    JGo_TX2_Partial.LocalFacts base seed err geometry query D hash ∧ Facts := by
  have inherited := JGq_PairCalls.on_saved saved same base seed err geometry query D hash realizes
  exact ⟨inherited.1,inherited.2.1,source⟩
#print axioms on_saved

def UnprovedPairGoal : Prop := FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
  (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=ok (.Ok JGo_TX2_Horner1_6.after)
#print UnprovedPairGoal
#print axioms AspisR1.JGs_K1.source
#print axioms AspisR1.JGs_K3.source
#print axioms AspisR1.JGs_K4.source
#print axioms AspisR1.JGs_Regular.source
#print axioms AspisR1.JGs_Inactive.source
#print axioms AspisR1.JGs_LibraProgram.source
#print axioms AspisR1.JGs_LibraForward.source
#print axioms AspisR1.JGs_LibraNative.step0
#print axioms AspisR1.JGs_LibraNative.step1
#print axioms AspisR1.JGs_LibraSource.source
#print axioms AspisR1.FJr_BodyPairMeaning.value
#print axioms AspisR1.FJv_Top.deployed
#check @AspisR1.FJv_Top.deployed
end AspisR1.JGs_Calls
end
