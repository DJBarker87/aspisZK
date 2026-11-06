import NLV_Emit_finishPending
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_query (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_query cfg i g p a geom pending) before =
 SdkC_Source.run h (NLV_Tree.suffix_query cfg i g p a geom pending) before := by
 unfold NLV_Emitted.suffix_query NLV_Tree.suffix_query
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending])
#print axioms eq_query
end AspisR1.NLV_EmitProof
end
