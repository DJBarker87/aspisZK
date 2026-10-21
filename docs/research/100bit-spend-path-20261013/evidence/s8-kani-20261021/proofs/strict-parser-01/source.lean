import S8OwnedP6QMParserTransport
import R1CandidateStrictQM31Parser

set_option autoImplicit false
namespace AspisR1.S8OwnedP6StrictParser
open Aeneas Aeneas.Std Result
open AspisR1.S8OwnedP6FieldParserTransport
open AspisR1.RetainedFieldByteCodec

def qFromCandidate (x : CandidateQ) : ActualQ :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

def limbsToActual (limbs : QM31Limbs) : ActualQ :=
  qFromCandidate (AspisR1.CandidateStrictQM31Parser.limbsToCandidate limbs)

theorem roundtrip_result (r : Result (Option ActualQ)) :
    mapResult (Option.map qFromCandidate)
      (mapResult (Option.map qToCandidate) r) = r := by
  cases r with
  | ok value => cases value <;> rfl
  | fail e => rfl
  | div => rfl

/-- The actual extracted indexed decoder uses the unchanged retained strict
sixteen-byte codec, with literal coordinate rewrapping only. -/
theorem source_refines (arr : Array U8 16#usize) :
    S8OwnedP6.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr) =
      .ok ((decodeQM31LE
        (AspisR1.CandidateParserByteOrder.arrayBytes16 arr)).map limbsToActual) := by
  have h := AspisR1.S8OwnedP6QMParserTransport.qm_parser_eq (Array.to_slice arr)
  rw [AspisR1.CandidateStrictQM31Parser.source_refines] at h
  have back := congrArg (mapResult (Option.map qFromCandidate)) h
  rw [roundtrip_result] at back
  simp only [mapResult, Option.map_map, Function.comp_def] at back
  have hmap : (fun x => qFromCandidate
      (AspisR1.CandidateStrictQM31Parser.limbsToCandidate x)) = limbsToActual := rfl
  rw [hmap] at back
  exact back

/-- Successful actual field decoding determines the canonical retained limbs
of the exact original sixteen input bytes. -/
theorem success_has_strict_limbs (arr : Array U8 16#usize) (q : ActualQ)
    (h : S8OwnedP6.aspis_core.field.QM31.from_le_bytes
      (Array.to_slice arr) = .ok (some q)) :
    ∃ limbs : QM31Limbs,
      decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) = some limbs ∧
      q = limbsToActual limbs ∧
      encodeQM31LE limbs = AspisR1.CandidateParserByteOrder.arrayBytes16 arr := by
  rw [source_refines] at h
  cases hd : decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 arr) with
  | none => simp [hd] at h
  | some limbs =>
    have hq : limbsToActual limbs = q := by simpa only [hd, Option.map_some,
      Result.ok.injEq, Option.some.injEq] using h
    exact ⟨limbs, rfl, hq.symm, encodeQM31LE_of_decodeQM31LE _ _ hd⟩

#print axioms roundtrip_result
#print axioms source_refines
#print axioms success_has_strict_limbs
end AspisR1.S8OwnedP6StrictParser
