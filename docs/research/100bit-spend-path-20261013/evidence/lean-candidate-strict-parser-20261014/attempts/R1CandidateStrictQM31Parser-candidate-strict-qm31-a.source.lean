import R1CandidateParserByteOrder

/-! Compare the fixed-array candidate QM31 parser with the retained strict
    sixteen-byte/four-canonical-limb decoder. -/
set_option autoImplicit false

namespace AspisR1.CandidateStrictQM31Parser

open Aeneas Aeneas.Std
open AspisR1.RetainedFieldByteCodec

def limbsToCandidate (limbs : QM31Limbs) :
    AspisR1CandidateParser.field.QM31 :=
  { c0 :=
      { a := AspisR1.M31ParserRefinement.valueToU32 (limbs 0),
        b := AspisR1.M31ParserRefinement.valueToU32 (limbs 1) },
    c1 :=
      { a := AspisR1.M31ParserRefinement.valueToU32 (limbs 2),
        b := AspisR1.M31ParserRefinement.valueToU32 (limbs 3) } }

theorem decoder_refines (arr : Array U8 16#usize) :
    AspisR1.CandidateQM31Parser.decodeQM31 arr =
      (decodeQM31LE (AspisR1.CandidateParserByteOrder.arrayBytes16 arr)).map
        limbsToCandidate := by
  let bytes := AspisR1.CandidateParserByteOrder.arrayBytes16 arr
  let limbCanonical := fun (i : Fin 4) =>
    ((decodeWordLE (qm31LimbBytes bytes i) : RawWord) : Nat) < m31Modulus
  by_cases hcanonical : ∀ i, limbCanonical i
  · let limbs : QM31Limbs := fun i =>
      ⟨(decodeWordLE (qm31LimbBytes bytes i) : RawWord), hcanonical i⟩
    have h0 :
        AspisR1.RetainedFieldByteCodec.decodeM31LE
          (AspisR1.M31ParserArray.arrayBytes
            (AspisR1.CandidateCM31Parser.half0
              (AspisR1.CandidateQM31Parser.half0 arr))) = some (limbs 0) := by
      rw [AspisR1.CandidateParserByteOrder.half00_bytes]
      simp [AspisR1.RetainedFieldByteCodec.decodeM31LE, limbs, limbCanonical,
        hcanonical]
    have h1 :
        AspisR1.RetainedFieldByteCodec.decodeM31LE
          (AspisR1.M31ParserArray.arrayBytes
            (AspisR1.CandidateCM31Parser.half1
              (AspisR1.CandidateQM31Parser.half0 arr))) = some (limbs 1) := by
      rw [AspisR1.CandidateParserByteOrder.half10_bytes]
      simp [AspisR1.RetainedFieldByteCodec.decodeM31LE, limbs, limbCanonical,
        hcanonical]
    have h2 :
        AspisR1.RetainedFieldByteCodec.decodeM31LE
          (AspisR1.M31ParserArray.arrayBytes
            (AspisR1.CandidateCM31Parser.half0
              (AspisR1.CandidateQM31Parser.half1 arr))) = some (limbs 2) := by
      rw [AspisR1.CandidateParserByteOrder.half01_bytes]
      simp [AspisR1.RetainedFieldByteCodec.decodeM31LE, limbs, limbCanonical,
        hcanonical]
    have h3 :
        AspisR1.RetainedFieldByteCodec.decodeM31LE
          (AspisR1.M31ParserArray.arrayBytes
            (AspisR1.CandidateCM31Parser.half1
              (AspisR1.CandidateQM31Parser.half1 arr))) = some (limbs 3) := by
      rw [AspisR1.CandidateParserByteOrder.half11_bytes]
      simp [AspisR1.RetainedFieldByteCodec.decodeM31LE, limbs, limbCanonical,
        hcanonical]
    have hcand : AspisR1.CandidateQM31Parser.decodeQM31 arr =
        some (limbsToCandidate limbs) := by
      simp [AspisR1.CandidateQM31Parser.decodeQM31,
        AspisR1.CandidateCM31Parser.decodeCM31, limbsToCandidate,
        h0, h1, h2, h3]
    have hstrict : decodeQM31LE bytes = some limbs := by
      simp [AspisR1.RetainedFieldByteCodec.decodeQM31LE, limbs,
        limbCanonical, hcanonical]
    rw [hcand, hstrict]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.mp hcanonical
    have hbad : decodeM31LE (qm31LimbBytes bytes i) = none := by
      simp [AspisR1.RetainedFieldByteCodec.decodeM31LE, limbCanonical, hi]
    have hcand : AspisR1.CandidateQM31Parser.decodeQM31 arr = none := by
      fin_cases i <;>
        simp [AspisR1.CandidateQM31Parser.decodeQM31,
          AspisR1.CandidateCM31Parser.decodeCM31,
          AspisR1.CandidateParserByteOrder.half00_bytes,
          AspisR1.CandidateParserByteOrder.half10_bytes,
          AspisR1.CandidateParserByteOrder.half01_bytes,
          AspisR1.CandidateParserByteOrder.half11_bytes,
          hbad]
    have hstrict : decodeQM31LE bytes = none := by
      simp [AspisR1.RetainedFieldByteCodec.decodeQM31LE, hcanonical]
    rw [hcand, hstrict]
    rfl

theorem source_refines (arr : Array U8 16#usize) :
    AspisR1CandidateParser.field.QM31.from_le_bytes (Array.to_slice arr) =
      Result.ok ((decodeQM31LE
        (AspisR1.CandidateParserByteOrder.arrayBytes16 arr)).map
          limbsToCandidate) := by
  rw [AspisR1.CandidateQM31Parser.from_le_bytes_refines]
  exact congrArg Result.ok (decoder_refines arr)

#print axioms decoder_refines
#print axioms source_refines

end AspisR1.CandidateStrictQM31Parser
