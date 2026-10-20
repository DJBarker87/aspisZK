import PreparedPost25TranscriptTransport
import Post25OrdinaryCandidateSourceModel

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.Post25OrdinaryCallerAdapter

open AspisR1PublicPreparation.Post25TranscriptTransport

abbrev CandidateOps := AspisR1Post25Transcript.SamplerOps

def ordinaryCandidateOps : CandidateOps :=
  AspisR1Post25Transcript.OrdinaryCandidateSourceModel.operations
    (fun _ => .div) (fun _ => .div) (fun _ => .div)

private theorem candidate_scalar_false_congr {H : Type}
    (ops₁ ops₂ : CandidateOps) (D : CandidateDigest H)
    (self : CandidateTranscript H) (row : U8) (payload : Slice U8)
    (ho : ∀ bytes, ops₁.ordinary bytes = ops₂.ordinary bytes) :
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₁ D self row payload false =
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₂ D self row payload false := by
  cases h : AspisR1Post25Transcript.transcript.Transcript.block D self row payload with
  | ok pair =>
      rcases pair with ⟨block, after⟩
      simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h, ho,
        AspisR1Post25Transcript.trace.value]
  | fail e => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]
  | div => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]

/-- A current Prepared scalar false call with the candidate ordinary callback installed
through the explicit WideExact field map gives the retained ordinary row law. -/
theorem prepared_ordinary_scalar_success_model {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : CurrentDigest H) (self after : CurrentTranscript H)
    (row tag : U8) (payload : Slice U8) (out : CurrentWide)
    (htag : (160#u8 + row : Result U8) = .ok tag)
    (h : AspisR1PublicPreparation.PreparedModel.scalar
      (withCandidateScalars B ordinaryCandidateOps) D self row payload false =
      .ok (out, after)) :
    ∃ block absorbed state,
      (digestToCandidate D).digest (transcriptToCandidate self).hash
        (AspisR1Post25Transcript.TranscriptSuccess.absorbParts
          (transcriptToCandidate self).state tag payload) = .ok absorbed ∧
      (digestToCandidate D).digest (transcriptToCandidate self).hash
        (AspisR1Post25Transcript.TranscriptSuccess.readParts absorbed 1#u8) = .ok block ∧
      (digestToCandidate D).digest (transcriptToCandidate self).hash
        (AspisR1Post25Transcript.TranscriptSuccess.readParts absorbed 2#u8) = .ok state ∧
      transcriptToCandidate after =
        {transcriptToCandidate self with state := state} ∧
      AspisR1Post25Transcript.OrdinaryCandidateSourceModel.decode
        (wideToCandidate out) = R0C.ModuloField.ordinary
          (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  have hc := scalar_success_candidate_ops B ordinaryCandidateOps
    D self row payload false out after h
  have hcongr := candidate_scalar_false_congr ordinaryCandidateOps
    (AspisR1Post25Transcript.OrdinaryCandidateSourceModel.operations
      (fun _ => .div) (fun _ => .div) (fun _ => .div))
    (digestToCandidate D) (transcriptToCandidate self) row payload
    (by intro bytes; rfl)
  have hm : AspisR1Post25Transcript.transcript.Transcript.scalar
      (AspisR1Post25Transcript.OrdinaryCandidateSourceModel.operations
        (fun _ => .div) (fun _ => .div) (fun _ => .div))
      (digestToCandidate D) (transcriptToCandidate self) row payload false =
      .ok (wideToCandidate out, transcriptToCandidate after) := hcongr.symm.trans hc
  exact AspisR1Post25Transcript.OrdinaryCandidateSourceModel.scalar_model_success
    (digestToCandidate D) (fun _ => .div) (fun _ => .div) (fun _ => .div)
    (transcriptToCandidate self) (transcriptToCandidate after) row tag payload
    (wideToCandidate out) htag hm

#print axioms prepared_ordinary_scalar_success_model

end AspisR1PublicPreparation.Post25OrdinaryCallerAdapter
