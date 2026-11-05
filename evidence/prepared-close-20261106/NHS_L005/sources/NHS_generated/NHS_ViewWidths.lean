import NHL_PrepareDomain
import NHF_ViewInstalled
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_ViewWidths
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Fixed sourceView windows establish the actual scalar/query payload bounds. -/
theorem source (proof semantic y1 : Slice U8) (v : verifier.View)
 (size : 10055≤proof.val.length) (ySize : y1.val.length=928)
 (view : InstalledPreparation.sourceView proof semantic y1=ok (.Ok v)) :
 v.variant=.S2 ∧ v.y1.val.length=928 ∧ v.round0.val.length=224 ∧
 v.round1.val.length=224 ∧ v.final_message.val.length=2048 := by
 rw [NHF_ViewInstalled.result proof semantic y1 size] at view
 unfold NHF_ViewResult.model at view
 split at view
 · cases view
 · rename_i wide decoded
   have same := core.result.Result.Ok.inj (Result.ok.inj view)
   subst v
   change transport.Variant.S2=transport.Variant.S2 ∧ y1.val.length=928 ∧
     (NGV_ByteWindow.select proof 7527 224).val.length=224 ∧
     (NGV_ByteWindow.select proof 7783 224).val.length=224 ∧
     (NGV_ByteWindow.select proof 8007 2048).val.length=2048
   exact ⟨rfl,ySize,NGV_ByteWindow.select_length proof 7527 224 (by omega),
     NGV_ByteWindow.select_length proof 7783 224 (by omega),
     NGV_ByteWindow.select_length proof 8007 2048 (by omega)⟩
#print axioms source
end AspisR1.NHS_ViewWidths
