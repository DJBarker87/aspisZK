import NNG_WideView087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ViewShape087
open Aeneas Aeneas.Std Result NMP_prepare
open NNG_PrepareCarriers087

theorem shape (proof semantic y1 : Slice U8) (bound : 10055≤proof.val.length) (v : verifier.View)
 (returned : NNG_WideView087.call proof semantic y1=.ok (.Ok v)) :
 ∃ limbs : StrictWideByteCodec.WideLimbs,
 StrictWideByteCodec.decodeWideLE (WideParserArrayHalves.arrayBytes32 (NHF_ViewResult.input proof bound))=some limbs ∧
 v=viewBack (AspisR1SelectedWideViewV1.preparedView
  (NHF_ViewFinish.value proof semantic y1
   (AspisR1SelectedWideViewV1.parserCarrier (CandidateWideParserRefinement.limbsToCandidate limbs)) bound)) := by
 unfold NNG_WideView087.call at returned
 rw [NHF_ViewResult.result proof semantic y1 bound] at returned
 unfold NHF_ViewResult.model at returned
 cases h : StrictWideByteCodec.decodeWideLE (WideParserArrayHalves.arrayBytes32 (NHF_ViewResult.input proof bound)) with
 | none=>
   simp only [h,NMP_ResultTransport.outer,NMP_ResultTransport.inner] at returned
   cases returned
 | some limbs=>
   simp only [h,NMP_ResultTransport.outer,NMP_ResultTransport.inner] at returned
   exact ⟨limbs,h,(core.result.Result.Ok.inj (Result.ok.inj returned)).symm⟩

theorem borrowed (proof semantic y1 : Slice U8) (bound : 10055≤proof.val.length) (v : verifier.View)
 (returned : NNG_WideView087.call proof semantic y1=.ok (.Ok v)) : v.semantic=semantic ∧ v.y1=y1 := by
 obtain ⟨limbs,_,same⟩ := shape proof semantic y1 bound v returned
 subst v
 exact ⟨rfl,rfl⟩

theorem dimensions (proof semantic y1 : Slice U8) (bound : 10055≤proof.val.length) (v : verifier.View)
 (returned : NNG_WideView087.call proof semantic y1=.ok (.Ok v)) :
 v.round0.val.length=224 ∧ v.round1.val.length=224 ∧
 v.folded_root.isSome=true ∧ v.final_message.val.length=2048 := by
 obtain ⟨limbs,_,same⟩ := shape proof semantic y1 bound v returned
 subst v
 refine ⟨?_,?_,rfl,?_⟩
 · exact NGV_ByteWindow.select_length proof 7527 224 (by omega)
 · exact NGV_ByteWindow.select_length proof 7783 224 (by omega)
 · exact NGV_ByteWindow.select_length proof 8007 2048 (by omega)
#print axioms shape
#print axioms borrowed
#print axioms dimensions
end AspisR1.NNG_ViewShape087
