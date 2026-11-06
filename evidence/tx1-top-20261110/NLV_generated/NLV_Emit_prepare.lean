import NLV_Emit_accumulator
import NLV_Tree
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_EmitProof
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
theorem eq_prepare (h : SdkC_Source.Parts → Result SdkC_Source.Digest) (cfg : Configuration) (i : Input) (g : Scratch) (before : SdkC_Source.Log) :
 SdkC_Source.run h (NLV_Emitted.suffix_prepare cfg i g) before =
 SdkC_Source.run h (NLV_Tree.suffix_prepare cfg i g) before := by
 unfold NLV_Emitted.suffix_prepare NLV_Tree.suffix_prepare
 simp only [Bind.bind,Pure.pure]
 apply NLV_RunLaws.same
 rintro ⟨r,after⟩ earlierLog
 cases r <;> simp only [NLV_Emitted.try_run,eq_accumulator,SdkC_Source.run]
#print axioms eq_prepare
end AspisR1.NLV_EmitProof
end
