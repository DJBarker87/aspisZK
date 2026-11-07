import NLV_Emit_query
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_pending (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_pending cfg i g p a geom) before =
 SdkC_Source.run h (NLV_Tree.suffix_pending cfg i g p a geom) before := by
 unfold NLV_Emitted.suffix_pending NLV_Tree.suffix_pending
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query])
#print axioms eq_pending
end AspisR1.NLV_EmitProof
end
