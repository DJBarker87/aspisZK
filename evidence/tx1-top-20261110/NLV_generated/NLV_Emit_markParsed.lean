import NLV_Emit_zero
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_markParsed (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input)  (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_markParsed cfg i) before =
 SdkC_Source.run h (NLV_Tree.suffix_markParsed cfg i) before := by
 unfold NLV_Emitted.suffix_markParsed NLV_Tree.suffix_markParsed
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap,eq_foldedCopy,eq_foldedSlice,eq_markPrepare,eq_accumulator,eq_prepare,eq_zero])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap,eq_foldedCopy,eq_foldedSlice,eq_markPrepare,eq_accumulator,eq_prepare,eq_zero])
#print axioms eq_markParsed
end AspisR1.NLV_EmitProof
end
