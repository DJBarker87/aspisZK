import R1CandidateQM31Parser

/-! Successful candidate decodes produce canonical M31 limbs.  These facts
    follow from the strict mathematical decoder and parser refinements alone. -/
set_option autoImplicit false

namespace AspisR1.CandidateFieldCanonicality

open Aeneas Aeneas.Std Result
open AspisR1.RetainedFieldByteCodec
open AspisR1.M31ParserRefinement

def cmCanonical (v : AspisR1CandidateParser.field.CM31) : Prop :=
  v.a.val < m31Modulus ∧ v.b.val < m31Modulus

def qmCanonical (v : AspisR1CandidateParser.field.QM31) : Prop :=
  cmCanonical v.c0 ∧ cmCanonical v.c1

theorem decodeCM31_success_canonical (arr : Array U8 8#usize)
    (value : AspisR1CandidateParser.field.CM31)
    (h : AspisR1.CandidateCM31Parser.decodeCM31 arr = some value) :
    cmCanonical value := by
  cases hx : decodeM31LE
      (AspisR1.M31ParserArray.arrayBytes
        (AspisR1.CandidateCM31Parser.half0 arr)) with
  | none => simp [AspisR1.CandidateCM31Parser.decodeCM31, hx] at h
  | some a =>
    cases hy : decodeM31LE
        (AspisR1.M31ParserArray.arrayBytes
          (AspisR1.CandidateCM31Parser.half1 arr)) with
    | none => simp [AspisR1.CandidateCM31Parser.decodeCM31, hx, hy] at h
    | some b =>
      simp [AspisR1.CandidateCM31Parser.decodeCM31, hx, hy] at h
      cases h
      constructor
      · simpa [cmCanonical, valueToU32_val] using a.isLt
      · simpa [cmCanonical, valueToU32_val] using b.isLt

theorem source_cm31_success_canonical (arr : Array U8 8#usize)
    (value : AspisR1CandidateParser.field.CM31)
    (h : AspisR1CandidateParser.field.CM31.from_le_bytes
      (Array.to_slice arr) = Result.ok (some value)) :
    cmCanonical value := by
  have hdecode : AspisR1.CandidateCM31Parser.decodeCM31 arr = some value := by
    rw [AspisR1.CandidateCM31Parser.from_le_bytes_refines] at h
    exact Result.ok.inj h
  exact decodeCM31_success_canonical arr value hdecode

theorem decodeQM31_success_canonical (arr : Array U8 16#usize)
    (value : AspisR1CandidateParser.field.QM31)
    (h : AspisR1.CandidateQM31Parser.decodeQM31 arr = some value) :
    qmCanonical value := by
  cases hx : AspisR1.CandidateCM31Parser.decodeCM31
      (AspisR1.CandidateQM31Parser.half0 arr) with
  | none => simp [AspisR1.CandidateQM31Parser.decodeQM31, hx] at h
  | some c0 =>
    cases hy : AspisR1.CandidateCM31Parser.decodeCM31
        (AspisR1.CandidateQM31Parser.half1 arr) with
    | none => simp [AspisR1.CandidateQM31Parser.decodeQM31, hx, hy] at h
    | some c1 =>
      simp [AspisR1.CandidateQM31Parser.decodeQM31, hx, hy] at h
      cases h
      constructor
      · exact decodeCM31_success_canonical
          (AspisR1.CandidateQM31Parser.half0 arr) c0 hx
      · exact decodeCM31_success_canonical
          (AspisR1.CandidateQM31Parser.half1 arr) c1 hy

theorem source_qm31_success_canonical (arr : Array U8 16#usize)
    (value : AspisR1CandidateParser.field.QM31)
    (h : AspisR1CandidateParser.field.QM31.from_le_bytes
      (Array.to_slice arr) = Result.ok (some value)) :
    qmCanonical value := by
  have hdecode : AspisR1.CandidateQM31Parser.decodeQM31 arr = some value := by
    rw [AspisR1.CandidateQM31Parser.from_le_bytes_refines] at h
    exact Result.ok.inj h
  exact decodeQM31_success_canonical arr value hdecode

#print axioms decodeCM31_success_canonical
#print axioms source_cm31_success_canonical
#print axioms decodeQM31_success_canonical
#print axioms source_qm31_success_canonical

end AspisR1.CandidateFieldCanonicality
