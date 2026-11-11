import RPv_FJa_PublicBounds
import PIN2W7_TranscriptCopy
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): restated on the PIN2 public transcript, as W7 did for every
consumer of the restated preparation lemmas.  W3c restated
`ActualPublicFieldBounds.public_transcript_fields_canonical` on the PIN2 emission
(`PIN2_NEWGATE_r1_semantic.public_transcript` of `PreparationBinding.toPIN2`).  Here the
premise `prepared` is the PIN2 `public_transcript` of `toPIN2 (preparationPublic s)`, with
`D` and `out` carried by the field copies of `PIN2W7_TranscriptCopy`; the binder types of
`D` and `out` are unchanged (frozen).  The conclusion is textually unchanged. -/
noncomputable section
namespace AspisR1.FJa_PublicOnPreparation
open Aeneas Aeneas.Std Result
/-- Exact installed semantic public and all FIz-required word bounds derive
from the SAME successful public transcript preparation. -/
theorem value {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize) (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (p : FJa_PublicCopy.Public)
    (prepared : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript
      (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest D)
      (AspisR1PublicPreparation.PreparationBinding.toPIN2
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)) hash c1=
      ok (.Ok (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.transcript out)))
    (constructed : FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      (FIq_Carriers.toPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))=ok p) :
    p=FJa_PublicCopy.native (AspisR1PublicPreparation.PreparationBinding.preparationPublic s) ∧ FJa_PublicBounds.Bounds p := by
  have same := Result.ok.inj ((FJa_PublicCopy.on_statement (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)).symm.trans constructed)
  subst p
  exact ⟨rfl,FJa_PublicBounds.from_raw s
    (AspisR1PublicPreparation.ActualPublicFieldBounds.public_transcript_fields_canonical
      (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.digest D) s hash c1
      (AspisR1PublicPreparation.PIN2W7_TranscriptCopy.transcript out) prepared)⟩
#print axioms value
end AspisR1.FJa_PublicOnPreparation
end
