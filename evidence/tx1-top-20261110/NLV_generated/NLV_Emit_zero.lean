import NLV_Emit_prepare
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_zero (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input)  (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_zero cfg i) before =
 SdkC_Source.run h (NLV_Tree.suffix_zero cfg i) before := by
 unfold NLV_Emitted.suffix_zero NLV_Tree.suffix_zero
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap,eq_foldedCopy,eq_foldedSlice,eq_markPrepare,eq_accumulator,eq_prepare])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap,eq_foldedCopy,eq_foldedSlice,eq_markPrepare,eq_accumulator,eq_prepare])
#print axioms eq_zero
end AspisR1.NLV_EmitProof
end
