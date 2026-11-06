import NLV_Emit_markMerkle
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_batch0 (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (root : Root) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_batch0 cfg i g p a root) before =
 SdkC_Source.run h (NLV_Tree.suffix_batch0 cfg i g p a root) before := by
 unfold NLV_Emitted.suffix_batch0 NLV_Tree.suffix_batch0
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle])
#print axioms eq_batch0
end AspisR1.NLV_EmitProof
end
