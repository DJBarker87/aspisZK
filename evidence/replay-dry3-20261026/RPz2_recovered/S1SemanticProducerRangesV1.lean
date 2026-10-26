import S1ExtractedRoundChildrenV1
import AspisR1DecodeKFullSuccessCanonicality
import SemanticCallSelectedCanonical
set_option autoImplicit false
namespace AspisS1SemanticArrayRanges
open Aeneas Aeneas.Std Result
open AspisS1ExtractedRoundChildren

/-- The same four raw coordinate ranges, with no polynomial or evaluator
imports needed merely to establish a decoder/sampler producer's ranges. -/
def Canonical (q : MainQM) : Prop :=
  AspisR1PublicPreparation.SemanticCallSelectedCanonical.SelectedCanonical
    (AspisR1PublicPreparation.SemanticCallSelectedCanonical.toSelected q)

theorem decoded_success_inv (n : Usize) (r : MainRecord) (offset : Usize)
    (out : Array MainQM n) (h : children.decode n r offset = ok (.Ok out)) :
    ∃ actual : Array DecodeQM n,
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n (recordToDecoder r) offset =
        ok (.Ok actual) ∧ decoderArrayToMain actual = out := by
  change decodeMain n r offset = _ at h
  unfold decodeMain at h
  cases hr : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n (recordToDecoder r) offset with
  | ok result =>
    cases result with
    | Ok actual =>
      simp only [hr, decoderResultToMain] at h
      exact ⟨actual, rfl, core.result.Result.Ok.inj (Result.ok.inj h)⟩
    | Err e => simp only [hr, decoderResultToMain] at h; cases h
  | fail e => simp only [hr, decoderResultToMain] at h; cases h
  | div => simp only [hr, decoderResultToMain] at h; cases h

theorem decoder_coordinates_canonical (q : DecodeQM)
    (h : AspisR1DecodeKCanonicalArrayInvariant.Canonical q) :
    Canonical (decoderQMToMain q) := by
  have hP : AspisR1DecodeKFullV10.aspis_core.field.P.val =
      AspisR1.ExtractedMaskTowerAdd.P := by
    unfold AspisR1DecodeKFullV10.aspis_core.field.P
    rfl
  rcases h with ⟨ha, hb, hc, hd⟩
  change (q.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      q.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P) ∧
    (q.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧
      q.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P)
  exact ⟨⟨hP ▸ ha, hP ▸ hb⟩, ⟨hP ▸ hc, hP ▸ hd⟩⟩

/-- Canonical coefficient ranges come from this concrete decoder's same
successful output, not an additional coefficient-array premise. -/
theorem decoded_members_canonical (n : Usize) (r : MainRecord) (offset : Usize)
    (out : Array MainQM n) (h : children.decode n r offset = ok (.Ok out)) :
    ∀ q ∈ out.val, Canonical q := by
  obtain ⟨actual, call, same⟩ := decoded_success_inv n r offset out h
  have all := AspisR1DecodeKFullSuccessCanonicality.decode_k_success_canonical
    n (recordToDecoder r) offset actual call
  subst out
  intro q hq
  obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hq
  subst q
  have hc := decoder_coordinates_canonical _
    (all ⟨i, by simpa [decoderArrayToMain, actual.property] using hi⟩)
  simpa only [decoderArrayToMain, List.getElem_map] using hc

#print axioms decoded_success_inv
#print axioms decoder_coordinates_canonical
#print axioms decoded_members_canonical
end AspisS1SemanticArrayRanges
