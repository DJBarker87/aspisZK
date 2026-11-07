import NLV_Emit_checkpoint
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_finishPending (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_finishPending cfg i p a pending) before =
 SdkC_Source.run h (NLV_Tree.suffix_finishPending cfg i p a pending) before := by
 unfold NLV_Emitted.suffix_finishPending NLV_Tree.suffix_finishPending
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint])
#print axioms eq_finishPending
end AspisR1.NLV_EmitProof
end
