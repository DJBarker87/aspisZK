import NLV_Emit_markCheckpoint
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_checkpoint (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_checkpoint cfg i p a) before =
 SdkC_Source.run h (NLV_Tree.suffix_checkpoint cfg i p a) before := by
 unfold NLV_Emitted.suffix_checkpoint NLV_Tree.suffix_checkpoint
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint])
#print axioms eq_checkpoint
end AspisR1.NLV_EmitProof
end
