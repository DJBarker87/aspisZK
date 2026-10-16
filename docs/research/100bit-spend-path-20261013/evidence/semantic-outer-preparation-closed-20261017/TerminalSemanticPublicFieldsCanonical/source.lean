import TerminalSemanticPublicPreparationCopy

set_option autoImplicit false
open Aeneas Aeneas.Std

namespace AspisR1TerminalDigestBindingCandidate.SemanticPublicFieldsCanonical
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy

abbrev M31 := AspisR1PublicSerializer.aspis_core.field.M31

private def digestEntry (d : Array M31 8#usize) (i : Fin 8) : M31 :=
  d.val[i.val]'(by simpa [d.property] using i.isLt)

private def frontierEntry (f : Array (Array M31 8#usize) 20#usize)
    (l : Fin 20) (i : Fin 8) : M31 :=
  (f.val[l.val]'(by simpa [f.property] using l.isLt)).val[i.val]'
    (by
      have hrow := (f.val[l.val]'(by simpa [f.property] using l.isLt)).property
      simpa [hrow] using i.isLt)

def digestValuesCanonical (d : Array M31 8#usize) : Prop :=
  ∀ i : Fin 8, (digestEntry d i).val < AspisR1.RetainedFieldByteCodec.m31Modulus

def frontierValuesCanonical (f : Array (Array M31 8#usize) 20#usize) : Prop :=
  ∀ l : Fin 20, ∀ i : Fin 8,
    (frontierEntry f l i).val < AspisR1.RetainedFieldByteCodec.m31Modulus

def candidateShape (p : SemanticPublic) : Prop :=
  (p.variant = pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer →
    p.withdrawal_amount = none) ∧
  (p.variant = pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal →
    p.recipient = none)

def copiedFieldsCanonical (p : SemanticPublic) : Prop :=
  digestValuesCanonical p.anchor ∧
  digestValuesCanonical p.nullifier ∧
  p.asset_id.val < AspisR1.RetainedFieldByteCodec.m31Modulus ∧
  digestValuesCanonical p.change ∧
  frontierValuesCanonical p.transition.live_snapshot.frontier ∧
  digestValuesCanonical p.transition.candidate_afterstate.next_root ∧
  frontierValuesCanonical p.transition.candidate_afterstate.next_frontier ∧
  (∀ r, p.recipient = some r → digestValuesCanonical r) ∧
  (∀ a, p.withdrawal_amount = some a → a.val < AspisR1.RetainedFieldByteCodec.m31Modulus)

theorem copyFromWhole_shape (w : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    candidateShape (copyFromWhole w) := by
  cases w <;> simp [candidateShape, copyFromWhole, privatePublicCopy, withdrawalPublicCopy]

theorem copied_fields_canonical_of_projection
    (p : SemanticPublic) (hshape : candidateShape p)
    (h : AspisR1.PublicSourceRaw.Canonical
      (AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw
        (toWholePublic p))) :
    copiedFieldsCanonical p := by
  cases p with
  | mk variant pool domain anchor nullifier asset recipient change amount transition =>
    cases variant with
    | PrivateTransfer =>
      simp only [toWholePublic,
        AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw,
        AspisR1PublicSerializer.RawBridge431.project,
        AspisR1PublicSerializer.RawBridge431.projectCommon,
        AspisR1.PublicRawCoreAgreement.fromCore,
        AspisR1.PublicRawCoreAgreement.fromCoreCommon,
        toWholeTransition, fromWholeTransition,
        AspisR1.PublicSourceRaw.Canonical,
        AspisR1.PublicSourceRaw.commonCanonical] at h
      rcases h with ⟨⟨ha, hn, hasset, hc, hsf, hnr, hnf⟩, hrec⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        have hx := ha i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · intro i
        have hx := hn i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.rawWord] using hasset
      · intro i
        have hx := hc i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · intro l i
        have hx := hsf l i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectFrontier,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          frontierEntry, digestEntry] using hx
      · intro i
        have hx := hnr i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · intro l i
        have hx := hnf l i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectFrontier,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          frontierEntry, digestEntry] using hx
      · cases recipient with
        | none =>
          intro r hr
          cases hr
        | some r0 =>
          intro r hr
          cases hr
          intro i
          have hx := hrec i
          simpa [Option.getD, AspisR1.PublicSourceRaw.fieldCanonical,
            AspisR1PublicSerializer.RawBridge431.projectDigest,
            AspisR1PublicSerializer.RawBridge431.rawWord_val,
            digestEntry] using hx
      · intro a ha
        have hnone := hshape.1 rfl
        rw [hnone] at ha
        cases ha
    | Withdrawal =>
      simp only [toWholePublic,
        AspisR1PublicSerializer.ExtractedPublicCheckedBridge432.projectRaw,
        AspisR1PublicSerializer.RawBridge431.project,
        AspisR1PublicSerializer.RawBridge431.projectCommon,
        AspisR1.PublicRawCoreAgreement.fromCore,
        AspisR1.PublicRawCoreAgreement.fromCoreCommon,
        toWholeTransition, fromWholeTransition,
        AspisR1.PublicSourceRaw.Canonical,
        AspisR1.PublicSourceRaw.commonCanonical] at h
      rcases h with ⟨⟨ha, hn, hasset, hc, hsf, hnr, hnf⟩, hamount⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        have hx := ha i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · intro i
        have hx := hn i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.rawWord] using hasset
      · intro i
        have hx := hc i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · intro l i
        have hx := hsf l i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectFrontier,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          frontierEntry, digestEntry] using hx
      · intro i
        have hx := hnr i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          digestEntry] using hx
      · intro l i
        have hx := hnf l i
        simpa [AspisR1.PublicSourceRaw.fieldCanonical,
          AspisR1PublicSerializer.RawBridge431.projectFrontier,
          AspisR1PublicSerializer.RawBridge431.projectDigest,
          AspisR1PublicSerializer.RawBridge431.rawWord,
          frontierEntry, digestEntry] using hx
      · intro r hr
        have hnone := hshape.2 rfl
        rw [hnone] at hr
        cases hr
      · cases amount with
        | none =>
          intro a ha
          cases ha
        | some a0 =>
          intro a ha
          cases ha
          simpa [AspisR1.PublicSourceRaw.fieldCanonical,
            AspisR1PublicSerializer.RawBridge431.rawWord_val] using hamount


theorem copyFromStatement_shape
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    candidateShape (copyFromStatement s) := by
  exact copyFromWhole_shape (AspisR1TerminalDecoder.PublicBinding.toSerializer s)

theorem actual_preparation_fields_canonical
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize)
    (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = Result.ok (.Ok out)) :
    copiedFieldsCanonical (copyFromStatement s) := by
  exact copied_fields_canonical_of_projection (copyFromStatement s)
    (copyFromStatement_shape s)
    (copied_candidate_projection_is_canonical D s hash c1 out h)

#print axioms copyFromWhole_shape
#print axioms copied_fields_canonical_of_projection
#print axioms copyFromStatement_shape
#print axioms actual_preparation_fields_canonical
end AspisR1TerminalDigestBindingCandidate.SemanticPublicFieldsCanonical
