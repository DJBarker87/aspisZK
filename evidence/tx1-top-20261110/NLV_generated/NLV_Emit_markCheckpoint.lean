import NLV_Emit_returned
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_markCheckpoint (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_markCheckpoint cfg i bytes) before =
 SdkC_Source.run h (NLV_Tree.suffix_markCheckpoint cfg i bytes) before := by
 unfold NLV_Emitted.suffix_markCheckpoint NLV_Tree.suffix_markCheckpoint
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned])
#print axioms eq_markCheckpoint
end AspisR1.NLV_EmitProof
end
