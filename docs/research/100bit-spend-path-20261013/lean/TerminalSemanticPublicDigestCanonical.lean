import TerminalSemanticPublicFieldsCanonical
import DigestFixedPrefixR0P

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1TerminalDigestBindingCandidate.SemanticPublicDigestCanonical
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
open AspisR1TerminalDigestBindingCandidate.SemanticPublicFieldsCanonical

abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic

private def digestEntry (d : Array M31 8#usize) (i : Fin 8) : M31 :=
  d.val[i.val]'(by simpa [d.property] using i.isLt)

private def frontierEntry (f : Array (Array M31 8#usize) 20#usize)
    (l : Fin 20) (i : Fin 8) : M31 :=
  (f.val[l.val]'(by simpa [f.property] using l.isLt)).val[i.val]'
    (by
      have hrow := (f.val[l.val]'(by simpa [f.property] using l.isLt)).property
      simpa [hrow] using i.isLt)

/-- Direct input contract consumed by the retained fixed-prefix and wrapper
suffix proofs: every digest row is canonical in the exact candidate carrier. -/
def DigestInputsCanonical (p : Public) : Prop :=
  AspisR1.DigestFixedPrefix.DigestWordsCanonical p.anchor ∧
  AspisR1.DigestFixedPrefix.DigestWordsCanonical p.nullifier ∧
  AspisR1.DigestFixedPrefix.DigestWordsCanonical p.change ∧
  (∀ r, p.recipient = some r → AspisR1.DigestFixedPrefix.DigestWordsCanonical r) ∧
  (∀ l : Fin 20, AspisR1.DigestFixedPrefix.DigestWordsCanonical
    (p.transition.live_snapshot.frontier.val[l.val]'(by
      simpa [p.transition.live_snapshot.frontier.property] using l.isLt))) ∧
  AspisR1.DigestFixedPrefix.DigestWordsCanonical p.transition.candidate_afterstate.next_root ∧
  (∀ l : Fin 20, AspisR1.DigestFixedPrefix.DigestWordsCanonical
    (p.transition.candidate_afterstate.next_frontier.val[l.val]'(by
      simpa [p.transition.candidate_afterstate.next_frontier.property] using l.isLt))) ∧
  p.asset_id.val < AspisR1.ExtractedMaskTowerAdd.P ∧
  (∀ a, p.withdrawal_amount = some a → a.val < AspisR1.ExtractedMaskTowerAdd.P)

theorem actual_preparation_digest_inputs_canonical
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize)
    (out : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = Result.ok (.Ok out)) :
    DigestInputsCanonical (copyFromStatement s) := by
  obtain ⟨ha, hn, hasset, hc, hsf, hroot, hnext, hrecipient, hamount⟩ :=
    actual_preparation_fields_canonical D s hash c1 out h
  have hmod : AspisR1.RetainedFieldByteCodec.m31Modulus =
      AspisR1.ExtractedMaskTowerAdd.P := by
    norm_num [AspisR1.RetainedFieldByteCodec.m31Modulus,
      AspisR1.RetainedFieldByteCodec.rawCandidateCount,
      AspisR1.ExtractedMaskTowerAdd.P,
      AspisR1.ExtractedMaskM31AddSub.P]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj := ha j
    change ((copyFromStatement s).anchor.val[j.val]'(by
      simpa [(copyFromStatement s).anchor.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · intro j
    have hj := hn j
    change ((copyFromStatement s).nullifier.val[j.val]'(by
      simpa [(copyFromStatement s).nullifier.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · intro j
    have hj := hc j
    change ((copyFromStatement s).change.val[j.val]'(by
      simpa [(copyFromStatement s).change.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · intro r hr
    have hx := hrecipient r hr
    intro j
    have hj := hx j
    change (r.val[j.val]'(by simpa [r.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · intro l
    have hx := hsf l
    let row := (copyFromStatement s).transition.live_snapshot.frontier.val[l.val]'
      (by simpa [(copyFromStatement s).transition.live_snapshot.frontier.property] using l.isLt)
    intro j
    have hj := hx j
    change (row.val[j.val]'(by simpa [row.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · intro j
    have hj := hroot j
    change ((copyFromStatement s).transition.candidate_afterstate.next_root.val[j.val]'
      (by simpa [(copyFromStatement s).transition.candidate_afterstate.next_root.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · intro l
    have hx := hnext l
    let row := (copyFromStatement s).transition.candidate_afterstate.next_frontier.val[l.val]'
      (by simpa [(copyFromStatement s).transition.candidate_afterstate.next_frontier.property] using l.isLt)
    intro j
    have hj := hx j
    change (row.val[j.val]'(by simpa [row.property] using j.isLt)).val <
      AspisR1.RetainedFieldByteCodec.m31Modulus at hj
    simpa [hmod] using hj
  · simpa [hmod] using hasset
  · intro a ha
    have hx := hamount a ha
    simpa [hmod] using hx

#print axioms actual_preparation_digest_inputs_canonical
end AspisR1TerminalDigestBindingCandidate.SemanticPublicDigestCanonical
