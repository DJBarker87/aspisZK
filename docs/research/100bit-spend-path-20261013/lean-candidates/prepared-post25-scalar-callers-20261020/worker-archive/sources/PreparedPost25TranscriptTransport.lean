import ExtractedOpeningRun
import Post25TranscriptExplicitSamplers

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1PublicPreparation.Post25TranscriptTransport

abbrev CurrentTranscript (H : Type) := AspisR1PublicPreparation.transcript.Transcript H
abbrev CandidateTranscript (H : Type) := AspisR1Post25Transcript.transcript.Transcript H
abbrev CurrentDigest (H : Type) := AspisR1PublicPreparation.aspis_core.Digest32 H
abbrev CandidateDigest (H : Type) := AspisR1Post25Transcript.aspis_core.Digest32 H
abbrev CurrentCM := AspisR1PublicPreparation.aspis_core.field.CM31
abbrev CandidateCM := AspisR1Post25Transcript.aspis_core.field.CM31
abbrev CurrentQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev CandidateQM := AspisR1Post25Transcript.aspis_core.field.QM31
abbrev CurrentWide := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev CandidateWide := AspisR1Post25Transcript.aspis_core.field.WideExact

def cmToCandidate (x : CurrentCM) : CandidateCM := ⟨x.a, x.b⟩
def qmToCandidate (x : CurrentQM) : CandidateQM := ⟨cmToCandidate x.c0, cmToCandidate x.c1⟩
def wideToCandidate (x : CurrentWide) : CandidateWide :=
  ⟨qmToCandidate x.c0, qmToCandidate x.c1⟩

def digestToCandidate {H : Type} (D : CurrentDigest H) : CandidateDigest H :=
  ⟨D.coremarkerCopyInst, D.digest⟩

def transcriptToCandidate {H : Type} (self : CurrentTranscript H) : CandidateTranscript H :=
  ⟨self.state, self.hash⟩

theorem block_map {H : Type} (D : CurrentDigest H)
    (self : CurrentTranscript H) (row : U8) (payload : Slice U8) :
    (do
      let (block, after) ← AspisR1PublicPreparation.transcript.Transcript.block
        D self row payload
      .ok (block, transcriptToCandidate after)) =
      AspisR1Post25Transcript.transcript.Transcript.block
        (digestToCandidate D) (transcriptToCandidate self) row payload := by
  cases self
  cases D
  simp [AspisR1PublicPreparation.transcript.Transcript.block,
    AspisR1PublicPreparation.transcript.Transcript.absorb,
    AspisR1Post25Transcript.transcript.Transcript.block,
    AspisR1Post25Transcript.transcript.Transcript.absorb,
    transcriptToCandidate, digestToCandidate]


def candidateSamplerOps (B : AspisR1PublicPreparation.PreparedModel.Boundaries) :
    AspisR1Post25Transcript.SamplerOps where
  gamma := fun bytes => do
    let x ← B.gamma bytes
    .ok (wideToCandidate x)
  ordinary := fun bytes => do
    let x ← B.ordinary bytes
    .ok (wideToCandidate x)
  qm31 := fun _ => .div
  embed := fun _ => .div

def cmToCurrent (x : CandidateCM) : CurrentCM := ⟨x.a, x.b⟩
def qmToCurrent (x : CandidateQM) : CurrentQM :=
  ⟨cmToCurrent x.c0, cmToCurrent x.c1⟩
def wideToCurrent (x : CandidateWide) : CurrentWide :=
  ⟨qmToCurrent x.c0, qmToCurrent x.c1⟩

theorem wide_roundtrip (x : CurrentWide) : wideToCurrent (wideToCandidate x) = x := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

theorem wide_roundtrip_other (x : CandidateWide) : wideToCandidate (wideToCurrent x) = x := by
  cases x with
  | mk c0 c1 => cases c0 with | mk a b => cases c1 with | mk c d => rfl

theorem scalar_map {H : Type} (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : CurrentDigest H) (self : CurrentTranscript H) (row : U8)
    (payload : Slice U8) (nonzero : Bool) :
    (do
      let (out, after) ← AspisR1PublicPreparation.PreparedModel.scalar B D self row payload nonzero
      .ok (wideToCandidate out, transcriptToCandidate after)) =
    AspisR1Post25Transcript.transcript.Transcript.scalar
      (candidateSamplerOps B) (digestToCandidate D) (transcriptToCandidate self)
      row payload nonzero := by
  cases h : AspisR1PublicPreparation.transcript.Transcript.block D self row payload with
  | ok pair =>
      rcases pair with ⟨block, after⟩
      have hc : AspisR1Post25Transcript.transcript.Transcript.block
          (digestToCandidate D) (transcriptToCandidate self) row payload =
          .ok (block, transcriptToCandidate after) := by
        simpa [h] using (block_map D self row payload).symm
      simp only [AspisR1PublicPreparation.PreparedModel.scalar,
        AspisR1Post25Transcript.transcript.Transcript.scalar, h, hc,
        bind_tc_ok]
      cases nonzero <;>
        simp [candidateSamplerOps, AspisR1PublicPreparation.trace.value,
          AspisR1Post25Transcript.trace.value]
  | fail e =>
      have hc : AspisR1Post25Transcript.transcript.Transcript.block
          (digestToCandidate D) (transcriptToCandidate self) row payload = .fail e := by
        simpa [h] using (block_map D self row payload).symm
      simp [AspisR1PublicPreparation.PreparedModel.scalar,
        AspisR1Post25Transcript.transcript.Transcript.scalar,
        candidateSamplerOps, h, hc]
  | div =>
      have hc : AspisR1Post25Transcript.transcript.Transcript.block
          (digestToCandidate D) (transcriptToCandidate self) row payload = .div := by
        simpa [h] using (block_map D self row payload).symm
      simp [AspisR1PublicPreparation.PreparedModel.scalar,
        AspisR1Post25Transcript.transcript.Transcript.scalar,
        candidateSamplerOps, h, hc]

theorem candidate_scalar_congr {H : Type}
    (ops₁ ops₂ : AspisR1Post25Transcript.SamplerOps) (D : CandidateDigest H)
    (self : CandidateTranscript H) (row : U8) (payload : Slice U8) (nonzero : Bool)
    (hg : ∀ bytes, ops₁.gamma bytes = ops₂.gamma bytes)
    (ho : ∀ bytes, ops₁.ordinary bytes = ops₂.ordinary bytes) :
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₁ D self row payload nonzero =
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₂ D self row payload nonzero := by
  cases h : AspisR1Post25Transcript.transcript.Transcript.block D self row payload with
  | ok pair =>
      rcases pair with ⟨block, after⟩
      cases nonzero <;>
        simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h, hg, ho,
          AspisR1Post25Transcript.trace.value]
  | fail e => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]
  | div => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]

theorem scalar_map_to_ops {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (ops : AspisR1Post25Transcript.SamplerOps) (D : CurrentDigest H)
    (self : CurrentTranscript H) (row : U8) (payload : Slice U8) (nonzero : Bool)
    (hg : ∀ bytes, ops.gamma bytes = (candidateSamplerOps B).gamma bytes)
    (ho : ∀ bytes, ops.ordinary bytes = (candidateSamplerOps B).ordinary bytes) :
    (do
      let (out, after) ← AspisR1PublicPreparation.PreparedModel.scalar B D self row payload nonzero
      .ok (wideToCandidate out, transcriptToCandidate after)) =
    AspisR1Post25Transcript.transcript.Transcript.scalar
      ops (digestToCandidate D) (transcriptToCandidate self) row payload nonzero := by
  calc
    _ = AspisR1Post25Transcript.transcript.Transcript.scalar
        (candidateSamplerOps B) (digestToCandidate D) (transcriptToCandidate self)
        row payload nonzero := scalar_map B D self row payload nonzero
    _ = AspisR1Post25Transcript.transcript.Transcript.scalar
        ops (digestToCandidate D) (transcriptToCandidate self) row payload nonzero := by
      apply candidate_scalar_congr
      · intro bytes; exact (hg bytes).symm
      · intro bytes; exact (ho bytes).symm

def withCandidateScalars (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (ops : AspisR1Post25Transcript.SamplerOps) :
    AspisR1PublicPreparation.PreparedModel.Boundaries :=
  { B with
    gamma := fun bytes => do
      let x ← ops.gamma bytes
      .ok (wideToCurrent x)
    ordinary := fun bytes => do
      let x ← ops.ordinary bytes
      .ok (wideToCurrent x) }

theorem scalar_map_with_candidate_ops {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (ops : AspisR1Post25Transcript.SamplerOps) (D : CurrentDigest H)
    (self : CurrentTranscript H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
    (do
      let (out, after) ← AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B ops) D self row payload nonzero
      .ok (wideToCandidate out, transcriptToCandidate after)) =
    AspisR1Post25Transcript.transcript.Transcript.scalar
      ops (digestToCandidate D) (transcriptToCandidate self) row payload nonzero := by
  apply scalar_map_to_ops
  · intro bytes
    cases h : ops.gamma bytes <;>
      simp [candidateSamplerOps, withCandidateScalars, h, wide_roundtrip_other]
  · intro bytes
    cases h : ops.ordinary bytes <;>
      simp [candidateSamplerOps, withCandidateScalars, h, wide_roundtrip_other]

theorem scalar_success_candidate_ops {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (ops : AspisR1Post25Transcript.SamplerOps) (D : CurrentDigest H)
    (self : CurrentTranscript H) (row : U8) (payload : Slice U8) (nonzero : Bool)
    (out : CurrentWide) (after : CurrentTranscript H)
    (h : AspisR1PublicPreparation.PreparedModel.scalar
      (withCandidateScalars B ops) D self row payload nonzero = .ok (out, after)) :
    AspisR1Post25Transcript.transcript.Transcript.scalar
      ops (digestToCandidate D) (transcriptToCandidate self) row payload nonzero =
      .ok (wideToCandidate out, transcriptToCandidate after) := by
  have heq := scalar_map_with_candidate_ops B ops D self row payload nonzero
  simpa [h] using heq.symm

#print axioms block_map
#print axioms scalar_map
#print axioms wide_roundtrip
#print axioms scalar_map_to_ops
#print axioms scalar_map_with_candidate_ops
#print axioms scalar_success_candidate_ops

end AspisR1PublicPreparation.Post25TranscriptTransport
