import RPt_FIq_S_RawSemanticFieldOwnerAdapter
import AspisR1DecodeKFullSuccessCanonicality

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter

abbrev DecodeQM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev DecodeRecord := AspisR1DecodeKFullV10.r1_wire.ValidatedRecord
abbrev DecodeError := AspisR1DecodeKFullV10.r1_wire.Error
abbrev MainRecord := AspisR1PublicPreparation.r1_wire.ValidatedRecord
abbrev MainError := AspisR1PublicPreparation.r1_wire.Error

def recordToDecoder (r : MainRecord) : DecodeRecord := ⟨r.row, r.framed⟩

def decoderQMToMain (q : DecodeQM) : MainQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def decoderArrayToMain {n : Usize} (a : Array DecodeQM n) : Array MainQM n :=
  ⟨a.val.map decoderQMToMain, by simpa using a.property⟩

def decoderErrorToMain : DecodeError → MainError
  | .Allocation => .Allocation
  | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow
  | .Tag row => .Tag row
  | .Length row => .Length row
  | .NonCanonical row offset => .NonCanonical row offset
  | .Boundary round => .Boundary round
  | .Terminal => .Terminal
  | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes
  | .Public => .Public

def decoderResultToMain (n : Usize) :
    Result (core.result.Result (Array DecodeQM n) DecodeError) →
      Result (core.result.Result (Array MainQM n) MainError)
  | .ok (.Ok a) => .ok (.Ok (decoderArrayToMain a))
  | .ok (.Err e) => .ok (.Err (decoderErrorToMain e))
  | .fail e => .fail e
  | .div => .div

/-- A nominal adapter around the pinned actual indexed decode_k body. -/
def decodeMain (n : Usize) (r : MainRecord) (offset : Usize) :
    Result (core.result.Result (Array MainQM n) MainError) :=
  decoderResultToMain n
    (AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n (recordToDecoder r) offset)

theorem decodeMain_success_inv
    (n : Usize) (r : MainRecord) (offset : Usize) (out : Array MainQM n)
    (h : decodeMain n r offset = .ok (.Ok out)) :
    ∃ actual : Array DecodeQM n,
      AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n (recordToDecoder r) offset =
        .ok (.Ok actual) ∧ decoderArrayToMain actual = out := by
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

theorem decoder_canonical_to_main (q : DecodeQM)
    (h : AspisR1DecodeKCanonicalArrayInvariant.Canonical q) :
    Canonical (mainToProbe (decoderQMToMain q)) := by
  have hP : AspisR1DecodeKFullV10.aspis_core.field.P.val = AspisR1.ExtractedMaskTowerAdd.P := by
    unfold AspisR1DecodeKFullV10.aspis_core.field.P
    rfl
  rcases h with ⟨ha, hb, hc, hd⟩
  change (q.c0.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧ q.c0.b.val < AspisR1.ExtractedMaskTowerAdd.P) ∧
    (q.c1.a.val < AspisR1.ExtractedMaskTowerAdd.P ∧ q.c1.b.val < AspisR1.ExtractedMaskTowerAdd.P)
  exact ⟨⟨hP ▸ ha, hP ▸ hb⟩, ⟨hP ▸ hc, hP ▸ hd⟩⟩

theorem decodeMain_success_canonical
    (n : Usize) (r : MainRecord) (offset : Usize) (out : Array MainQM n)
    (h : decodeMain n r offset = .ok (.Ok out)) :
    ∀ j : Fin n, Canonical (mainToProbe
      (out.val[j.val]'(by simpa [out.property] using j.isLt))) := by
  obtain ⟨actual, hactual, hout⟩ := decodeMain_success_inv n r offset out h
  have hall := AspisR1DecodeKFullSuccessCanonicality.decode_k_success_canonical
    n (recordToDecoder r) offset actual hactual
  subst out
  intro j
  simpa only [decoderArrayToMain, List.getElem_map] using
    decoder_canonical_to_main _ (hall j)

/-- The coefficient-canonicality premise of the semantic polynomial adapters
is discharged by actual successful decoding, for every array length. -/
theorem decodeMain_success_members_canonical
    (n : Usize) (r : MainRecord) (offset : Usize) (out : Array MainQM n)
    (h : decodeMain n r offset = .ok (.Ok out)) :
    ∀ q ∈ out.val, Canonical (mainToProbe q) := by
  have hall := decodeMain_success_canonical n r offset out h
  intro q hq
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hq
  subst q
  exact hall ⟨j, by simpa [out.property] using hj⟩

#print axioms decodeMain_success_inv
#print axioms decoder_canonical_to_main
#print axioms decodeMain_success_canonical
#print axioms decodeMain_success_members_canonical
end AspisR1PublicPreparation.RawActualDecodeKMainAdapter
