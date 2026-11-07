import NLV_Emit_parse
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_guard (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input)  (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_guard cfg i) before =
 SdkC_Source.run h (NLV_Tree.suffix_guard cfg i) before := by
 unfold NLV_Emitted.suffix_guard NLV_Tree.suffix_guard
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap,eq_foldedCopy,eq_foldedSlice,eq_markPrepare,eq_accumulator,eq_prepare,eq_zero,eq_markParsed,eq_scan,eq_parse])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry,eq_markMerkle,eq_batch0,eq_foldedUnwrap,eq_foldedCopy,eq_foldedSlice,eq_markPrepare,eq_accumulator,eq_prepare,eq_zero,eq_markParsed,eq_scan,eq_parse])
#print axioms eq_guard
end AspisR1.NLV_EmitProof
end
