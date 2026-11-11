import LIB_VPublicTranscript
import LIB_VPublicDomain
import PIN2_PublicSerializerWhole
import PIN2W7_TranscriptCopy
/-! PIN2 W10 (2026-11-11): `code_asset` reproved (statement unchanged) because
`LIB_VPublicTranscript.code` is now the PIN2 public transcript (approved definition change).
Route: run value = erase (publicTranscriptPIN2 ..) = copied-back PIN2 `public_transcript`
(`publicTranscriptPIN2_erasure`); its success gives PIN2 `public_bytes (toPIN2 a.1)` success
(`PIN2W7_TranscriptCopy.public_transcript_split`); the PIN2 serializer's `source_success`
(W3c `PIN2_PublicSerializerWhole`) proves the asset word canonical.  New helpers
`asset_step_PIN2`, `bytes_asset_PIN2`; release `asset_step`, `bytes_asset` kept unchanged. -/
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
 change (asset p) ∈ [asset p]
 exact List.mem_cons_self
/-- PIN2: the asset word is one instruction of the PIN2 serializer program on the copy. -/
theorem asset_step_PIN2 (p : Public) :
 AspisR1.PIN2_PublicBytesRefinement.Step.words (AspisR1.PIN2_PublicBytesRefinement.single (asset p)) ∈
  AspisR1.PIN2_PublicBytesRefinement.steps (PreparationBinding.toPIN2 p) := by
 cases p <;> simp [asset,AspisR1.PIN2_PublicBytesRefinement.steps,PreparationBinding.toPIN2,
  FIq_Carriers.toPublic,FIq_Carriers.toTransfer,FIq_Carriers.toWithdrawal,NKR_TermPublic.value]
/-- PIN2: success of the PIN2 serializer on the copy proves the asset word canonical. -/
theorem bytes_asset_PIN2 (p : Public) (bytes : alloc.vec.Vec U8)
 (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
   (PreparationBinding.toPIN2 p)=.ok (.Ok bytes)) : LIB_VPublicDomain.publicAssetDom p := by
 have canon := (AspisR1PublicSerializer.PIN2Whole.source_success _ _ h).1
 apply canon
 apply List.mem_flatMap.mpr
 refine ⟨_,asset_step_PIN2 p,?_⟩
 change (asset p) ∈ [asset p]
 exact List.mem_cons_self
/-- Internal returned-arm implication from the SAME producer in CLOSED131.
It is not a premise of the source/root or field law. -/
theorem code_asset (a : Public × RSL.B32) (env : RSL.Env) (t : Transcript)
 (h : (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2=.ok (.Ok t)) :
 LIB_VPublicDomain.publicAssetDom a.1 := by
 rw [LIB_VPublicTranscript.source,PreparedHashCode.run_value,S1SemanticCode.publicTranscriptPIN2_erasure] at h
 cases hp : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest (LIB_VCode.digest env))
   (PreparationBinding.toPIN2 a.1) () (LIB_Env.nativeKey a.2) with
 | fail e => rw [hp] at h;cases h
 | div => rw [hp] at h;cases h
 | ok reply =>
  cases reply with
  | Err e => rw [hp] at h;cases h
  | Ok t' =>
   obtain ⟨bytes,hs,_⟩ := PIN2W7_TranscriptCopy.public_transcript_split (LIB_VCode.digest env)
     (PreparationBinding.toPIN2 a.1) () (LIB_Env.nativeKey a.2) (PIN2W7_PrefixGlue.transcriptBack t') hp
   exact bytes_asset_PIN2 a.1 bytes hs
#print axioms asset_step
#print axioms bytes_asset
#print axioms asset_step_PIN2
#print axioms bytes_asset_PIN2
#print axioms code_asset
end LIB_VPublicAsset
