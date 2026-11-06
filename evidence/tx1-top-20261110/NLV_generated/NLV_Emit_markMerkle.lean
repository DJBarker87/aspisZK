import NLV_Emit_geometry
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_markMerkle (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_markMerkle cfg i g p a) before =
 SdkC_Source.run h (NLV_Tree.suffix_markMerkle cfg i g p a) before := by
 unfold NLV_Emitted.suffix_markMerkle NLV_Tree.suffix_markMerkle
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (solve | simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry])
 | (apply NLV_RunLaws.same; intro reply earlierLog)
 | (split <;> simp only [NLV_Emitted.try_run,eq_returned,eq_markCheckpoint,eq_checkpoint,eq_finishPending,eq_query,eq_pending,eq_geometry])
#print axioms eq_markMerkle
end AspisR1.NLV_EmitProof
end
