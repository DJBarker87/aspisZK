import NDO_JGx_CommonSuccess
import NDO_JGx_Tail
import NDO_JGx_StageDictionary
import NDO_JGx_QueryFinishOnly
import NDO_JGx_Batch
import NDO_JGx_Folded
import NDO_JGx_Inactive
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Common
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.publicInput JFx_NativeBytes.checkpoint JFw_Frames.window

theorem source {C Hash : Type} (base : VTop_Stages.Ops) (seed : FinishOps FIo_Install.W)
    (err : C) (geometry : Port3_NativeGeometryBody.Ops C) (query : Port3_NativeQueryBody.Ops)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (realizes : JFn_HashBoundary.Realizes JFp_SHADigest.digest) :
    VTop_Stages.verifier.candidate.tx2_common (JGx_StageDictionary.source base seed err geometry query)
      (JFn_HashBoundary.dictionary JFp_SHADigest.digest D) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof JFx_NativeBytes.checkpoint hash none=ok (.Ok ()) := by
  obtain ⟨inactive,decoded⟩ := JGx_Inactive.source
  obtain ⟨a,b,flushed,call,flush,finish⟩ := JGx_QueryFinishOnly.source base seed err geometry query
  apply JGx_CommonSuccess.source (JGx_StageDictionary.source base seed err geometry query)
    (JFn_HashBoundary.dictionary JFp_SHADigest.digest D) hash JFx_NativeBytes.publicInput
    JFx_NativeBytes.proof JFx_NativeBytes.checkpoint JFo_Prepared.value JFo_Prepared.accumulator a
    JFr_TX2_Powers.value inactive (JFw_Frames.window 7495 32) (JFw_Frames.window 7751 32)
    JGe_View.folded (JFv_TX2_Geometry.value err geometry) JFo_Pending.value b
  · exact JFn_Resume.source JFp_SHADigest.digest D hash realizes
  · rfl
  · rfl
  · exact JFr_TX2_Powers.source
  · intro phase; rfl
  · rfl
  · rfl
  · exact JGx_Ranges.inactive
  · exact decoded
  · rfl
  · rfl
  · rfl
  · exact JGx_Folded.read
  · exact JGx_Folded.array
  · rfl
  · exact JGx_Batch.source D hash
  · exact JFv_TX2_Geometry.stage err geometry
  · exact JFo_Pending.source
  · exact call
  · exact JGx_Tail.source _ inactive a b flushed flush rfl rfl (finish inactive)
#print axioms source
end AspisR1.JGx_Common
end
