import NLV_Emit_foldedUnwrap
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_foldedCopy (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (slice : Slice U8) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_foldedCopy cfg i g p a slice) before =
 SdkC_Source.run h (NLV_Tree.suffix_foldedCopy cfg i g p a slice) before := by
 unfold NLV_Emitted.suffix_foldedCopy NLV_Tree.suffix_foldedCopy
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap])
#print axioms eq_foldedCopy
end AspisR1.NLV_EmitProof
end
