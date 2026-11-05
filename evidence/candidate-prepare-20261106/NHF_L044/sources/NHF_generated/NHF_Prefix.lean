import NHF_Recombine
import NHF_ViewInstalled
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHF_Prefix
open Aeneas Aeneas.Std Result NGV_ByteWindow
/-- The real emitted split exists from the actual allocation length; neither
its success nor either child output is an independent input premise. -/
theorem construct (proof : Slice U8) (logical : alloc.vec.Vec U8)
 (proofSize : proof.val.length=57607) (logicalSize : logical.val.length=14759) :
 ∃ parts : (Slice U8×Slice U8) × ((Slice U8×Slice U8)→Slice U8),
 ∃ semantic y1 : Slice U8,
 core.slice.Slice.split_at_mut (alloc.vec.Vec.deref_mut logical).1 13831#usize=ok parts ∧
 AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
   (select proof 16 7015) parts.1.1=ok (.Ok (),semantic) ∧
 NFU_Retarget.compact.expand_values (select proof 7031 464) parts.1.2=ok (.Ok (),y1) ∧
 semantic.val.length=13831 ∧ y1.val.length=928 ∧
 ((alloc.vec.Vec.deref_mut logical).2 (parts.2 (semantic,y1))).val=semantic.val++y1.val ∧
 AspisR1CurrentCaller.InstalledPreparation.sourceView proof semantic y1=
   ok (NHF_ViewInstalled.port (NHF_ViewResult.model proof semantic y1 (by omega))) := by
 have bound : 13831#usize ≤ (alloc.vec.Vec.deref_mut logical).1.length := by
  change 13831 ≤ logical.val.length
  omega
 obtain ⟨parts,splitRun,facts⟩:=WP.spec_imp_exists
  (core.slice.Slice.split_at_mut.spec (alloc.vec.Vec.deref_mut logical).1 13831#usize bound)
 have firstSize : parts.1.1.val.length=13831 := by simpa using facts.1
 have secondSize : parts.1.2.val.length=928 := by
  have h:=facts.2.1
  change parts.1.2.val.length=logical.val.length-13831 at h
  omega
 have semInput : (select proof 16 7015).val.length=7015 := select_length _ _ _ (by omega)
 have yInput : (select proof 7031 464).val.length=464 := select_length _ _ _ (by omega)
 obtain ⟨semantic,semRun,_,semSize,_⟩:=NGV_SemanticPacket.result
   (select proof 16 7015) parts.1.1 semInput firstSize
 obtain ⟨y1,yRun,_,ySize,_⟩:=NGV_ExpandAssociation.result
   (select proof 7031 464) parts.1.2 (by omega) (by rw [yInput]) (by rw [yInput,secondSize])
 have yFinal : y1.val.length=928 := ySize.trans secondSize
 have first : semantic.length=parts.1.1.length := semSize.trans firstSize.symm
 have second : y1.length=parts.1.2.length := ySize
 have back:=NHF_Recombine.bytes logical (alloc.vec.Vec.deref_mut logical) parts
   13831#usize semantic y1 rfl splitRun first second
 exact ⟨parts,semantic,y1,splitRun,semRun,yRun,semSize,yFinal,back,
   NHF_ViewInstalled.result proof semantic y1 (by omega)⟩
#print axioms construct
end AspisR1.NHF_Prefix
end
