import LIB_VPublicTranscript
import LIB_VPublicDomain
set_option autoImplicit false
noncomputable section
namespace LIB_VPublicAsset
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1 AspisR1PublicPreparation
open AspisR1PublicSerializer.Whole431 (Step sourceSteps single stepWords source_success)
abbrev asset (p : Public) := (NKR_TermPublic.value (FIq_Carriers.toPublic p)).asset_id
def assetStep (p : Public) : Step := .words (single (asset p))
theorem asset_step (p : Public) : assetStep p ∈ sourceSteps (SerializerWhole.toOld p) := by
 cases p <;> simp [assetStep,asset,sourceSteps,SerializerWhole.toOld,
  SerializerWhole.toTransfer,SerializerWhole.toWithdrawal,FIq_Carriers.toPublic,
  FIq_Carriers.toTransfer,FIq_Carriers.toWithdrawal,NKR_TermPublic.value]
theorem bytes_asset (p : Public) (bytes : alloc.vec.Vec U8)
 (h : p.public_bytes=.ok (.Ok bytes)) : LIB_VPublicDomain.publicAssetDom p := by
 have oldEq := SerializerWhole.serializer_eq p
 rw [h] at oldEq
 have old : (SerializerWhole.toOld p).public_bytes=.ok (.Ok bytes) := oldEq
 have canon := (source_success _ _ old).1
 apply canon
 apply List.mem_flatMap.mpr
 refine ⟨assetStep p,asset_step p,?_⟩
 simp [assetStep,stepWords,single]
/-- Internal returned-arm implication from the SAME producer in CLOSED131.
It is not a premise of the source/root or field law. -/
theorem code_asset (a : Public × RSL.B32) (env : RSL.Env) (t : Transcript)
 (h : (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2=.ok (.Ok t)) :
 LIB_VPublicDomain.publicAssetDom a.1 := by
 unfold LIB_VPublicTranscript.code NHG_PublicTranscript.packetCode at h
 cases produced : NHG_Serializer.computation a.1 with
 | fail e => simp only [NGX_CodeTrace.lift_bind,produced] at h;cases h
 | div => simp only [NGX_CodeTrace.lift_bind,produced] at h;cases h
 | ok result =>
  cases result with
  | Err e => simp only [NGX_CodeTrace.lift_bind,produced,NGX_CodeTrace.pure_run] at h;cases h
  | Ok bytes => exact bytes_asset a.1 bytes ((NHG_Serializer.source a.1).trans produced)
#print axioms asset_step
#print axioms bytes_asset
#print axioms code_asset
end LIB_VPublicAsset
