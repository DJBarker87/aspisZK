import NHF_Frame
import NGV_SemanticPacket
import NGV_ExpandAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_Expansions
open Aeneas Aeneas.Std Result NGV_ByteWindow
/-- Construct both callee outputs from the SAME stored proof and the two
actual prestate windows. No child success or independently chosen output is
assumed. The physical Vec/back-function association is a separate obligation. -/
theorem construct (proof logical : Slice U8)
 (proofSize : proof.val.length = 57607) (logicalSize : logical.val.length = 14759) :
 ∃ semantic y1 : Slice U8,
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
   (select proof 16 7015) (select logical 0 13831) = ok (.Ok (),semantic) ∧
 NFU_Retarget.compact.expand_values (select proof 7031 464) (select logical 13831 928) =
   ok (.Ok (),y1) ∧
 semantic.val.length = 13831 ∧ y1.val.length = 928 ∧
 (NHF_Frame.join semantic.val y1.val).length = 14759 ∧
 (NHF_Frame.join semantic.val y1.val).take 13831 = semantic.val ∧
 (NHF_Frame.join semantic.val y1.val).drop 13831 = y1.val := by
 have semInput : (select proof 16 7015).val.length=7015 :=
   select_length _ _ _ (by omega)
 have semOutput : (select logical 0 13831).val.length=13831 :=
   select_length _ _ _ (by omega)
 have yInput : (select proof 7031 464).val.length=464 :=
   select_length _ _ _ (by omega)
 have yOutput : (select logical 13831 928).val.length=928 :=
   select_length _ _ _ (by omega)
 obtain ⟨semantic,semRun,_,semLength,_⟩ := NGV_SemanticPacket.result
   (select proof 16 7015) (select logical 0 13831) semInput semOutput
 obtain ⟨y1,yRun,_,yLength,_⟩ := NGV_ExpandAssociation.result
   (select proof 7031 464) (select logical 13831 928)
   (by omega) (by rw [yInput];decide) (by rw [yInput,yOutput])
 have ySize : y1.val.length=928 := yLength.trans yOutput
 exact ⟨semantic,y1,semRun,yRun,semLength,ySize,
   NHF_Frame.logical_size _ _ semLength ySize,
   NHF_Frame.semantic_preserved _ _ semLength,NHF_Frame.y1_preserved _ _ semLength⟩
#print axioms construct
end AspisR1.NHF_Expansions
end
