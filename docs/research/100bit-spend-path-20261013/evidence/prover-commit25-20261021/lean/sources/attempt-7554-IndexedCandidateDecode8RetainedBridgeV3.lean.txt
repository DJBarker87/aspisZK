import AspisR1Post25Sampler.Funs
import R0C.ModuloField
import R1Z.ProverCommitArrayIndex25

/-! Candidate-only bridge from the freshly extracted ordinary sampler's
`decode8` result to the retained eight-limb `digitsField` representation.
The source correspondence remains the candidate extraction, not production. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3

open Aeneas Aeneas.Std Result
open AspisR1Post25Sampler
open AspisV8R15.ExactTowerBase
open AspisWideTower

abbrev CandidateQM := AspisR1Post25Sampler.field.QM31
abbrev CandidateWide := AspisR1Post25Sampler.field.WideExact

def candidateQMToExact (v : CandidateQM) : QM31Exact :=
  ⟨⟨(v.c0.a.val : M31Exact), (v.c0.b.val : M31Exact)⟩,
   ⟨(v.c1.a.val : M31Exact), (v.c1.b.val : M31Exact)⟩⟩

def candidateWideToExact (v : CandidateWide) : WideExact :=
  ⟨candidateQMToExact v.c0, candidateQMToExact v.c1⟩

private def digitAt (digits : Array U32 8#usize) (i : Fin 8) : U32 :=
  digits.val[i.val]'(by simpa [digits.property] using i.isLt)

def retainedDigits (digits : Array U32 8#usize)
    (hcanonical : ∀ i : Fin 8, (digitAt digits i).val < AspisV8R15.ExactTowerBase.P) :
    Fin 8 → Fin AspisV8R15.ExactTowerBase.P :=
  fun i => ⟨(digitAt digits i).val, hcanonical i⟩

private theorem index_ok (digits : Array U32 8#usize) (i : Usize)
    (hi : i.val < 8) :
    Array.index_usize digits i =
      .ok (digits.val[i.val]'(by simpa [digits.property] using hi)) :=
  R1Z.ProverCommitArrayIndex25.array_index_usize_ok digits i hi

private def reduced (x : U32) : U32 :=
  ⟨BitVec.umod x.bv (2147483647#u32).bv⟩

private theorem rem_success (x : U32) : (x % field.P : Result U32) = .ok (reduced x) := by
  unfold field.P
  rfl

private theorem reduced_val (x : U32) :
    (reduced x).val = x.val % 2147483647 := by
  change (x.bv % (2147483647#32)).toNat = x.bv.toNat % 2147483647
  rw [BitVec.toNat_umod]
  rfl

private theorem reduced_eq_self (x : U32) (hx : x.val < 2147483647) :
    reduced x = x := by
  apply UScalar.eq_of_val_eq
  rw [reduced_val, Nat.mod_eq_of_lt hx]

private theorem canonical_success (q : CandidateQM)
    (h0 : q.c0.a.val < 2147483647) (h1 : q.c0.b.val < 2147483647)
    (h2 : q.c1.a.val < 2147483647) (h3 : q.c1.b.val < 2147483647) :
    field.canonical_qm31 q = .ok q := by
  have r0 : (q.c0.a % field.P : Result U32) = .ok q.c0.a := by
    rw [rem_success, reduced_eq_self _ h0]
  have r1 : (q.c0.b % field.P : Result U32) = .ok q.c0.b := by
    rw [rem_success, reduced_eq_self _ h1]
  have r2 : (q.c1.a % field.P : Result U32) = .ok q.c1.a := by
    rw [rem_success, reduced_eq_self _ h2]
  have r3 : (q.c1.b % field.P : Result U32) = .ok q.c1.b := by
    rw [rem_success, reduced_eq_self _ h3]
  simp only [field.canonical_qm31,
    field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    r0, r1, r2, r3, bind_tc_ok]

private theorem digitsField_candidate (digits : Array U32 8#usize)
    (hcanonical : ∀ i : Fin 8, (digitAt digits i).val < AspisV8R15.ExactTowerBase.P) :
    candidateWideToExact
      ⟨⟨⟨digitAt digits 0, digitAt digits 1⟩,
         ⟨digitAt digits 2, digitAt digits 3⟩⟩,
       ⟨⟨digitAt digits 4, digitAt digits 5⟩,
         ⟨digitAt digits 6, digitAt digits 7⟩⟩⟩ =
      R0C.ModuloField.digitsField (retainedDigits digits hcanonical) := by
  rw [R0C.ModuloField.digitsField_apply]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [candidateWideToExact, candidateQMToExact, retainedDigits,
        digitAt, R0C.ModuloField.digitsField_apply,
        AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv,
        AspisV8R19.R599CanonicalFieldTuple.tupleField,
        AspisV8R19.SamplerFieldDecode.decode4]
  · apply QuadraticAlgebra.ext <;>
      simp [candidateWideToExact, candidateQMToExact, retainedDigits,
        digitAt, R0C.ModuloField.digitsField_apply,
        AspisV8R19.R599CanonicalFieldTuple.tupleFieldEquiv,
        AspisV8R19.R599CanonicalFieldTuple.tupleField,
        AspisV8R19.SamplerFieldDecode.decode4]

/-- For canonical limbs, the exact extracted `decode8` computation succeeds
and its value, interpreted as the retained tower, is `digitsField`. -/
theorem decode8_candidate_eq_retained (digits : Array U32 8#usize)
    (hcanonical : ∀ i : Fin 8, (digitAt digits i).val < AspisV8R15.ExactTowerBase.P) :
    ∃ value : CandidateWide,
      sampler.decode8 digits = .ok value ∧
      candidateWideToExact value =
        R0C.ModuloField.digitsField (retainedDigits digits hcanonical) := by
  let d0 := digitAt digits 0
  let d1 := digitAt digits 1
  let d2 := digitAt digits 2
  let d3 := digitAt digits 3
  let d4 := digitAt digits 4
  let d5 := digitAt digits 5
  let d6 := digitAt digits 6
  let d7 := digitAt digits 7
  have i0 : Array.index_usize digits 0#usize = .ok d0 := by
    simpa [d0, digitAt] using index_ok digits 0#usize (by decide)
  have i1 : Array.index_usize digits 1#usize = .ok d1 := by
    simpa [d1, digitAt] using index_ok digits 1#usize (by decide)
  have i2 : Array.index_usize digits 2#usize = .ok d2 := by
    simpa [d2, digitAt] using index_ok digits 2#usize (by decide)
  have i3 : Array.index_usize digits 3#usize = .ok d3 := by
    simpa [d3, digitAt] using index_ok digits 3#usize (by decide)
  have i4 : Array.index_usize digits 4#usize = .ok d4 := by
    simpa [d4, digitAt] using index_ok digits 4#usize (by decide)
  have i5 : Array.index_usize digits 5#usize = .ok d5 := by
    simpa [d5, digitAt] using index_ok digits 5#usize (by decide)
  have i6 : Array.index_usize digits 6#usize = .ok d6 := by
    simpa [d6, digitAt] using index_ok digits 6#usize (by decide)
  have i7 : Array.index_usize digits 7#usize = .ok d7 := by
    simpa [d7, digitAt] using index_ok digits 7#usize (by decide)
  have hc0 : field.canonical_qm31 ⟨⟨d0,d1⟩,⟨d2,d3⟩⟩ =
      .ok ⟨⟨d0,d1⟩,⟨d2,d3⟩⟩ := by
    refine canonical_success _ ?_ ?_ ?_ ?_
    · simpa [d0] using hcanonical ⟨0, by decide⟩
    · simpa [d1] using hcanonical ⟨1, by decide⟩
    · simpa [d2] using hcanonical ⟨2, by decide⟩
    · simpa [d3] using hcanonical ⟨3, by decide⟩
  have hc1 : field.canonical_qm31 ⟨⟨d4,d5⟩,⟨d6,d7⟩⟩ =
      .ok ⟨⟨d4,d5⟩,⟨d6,d7⟩⟩ := by
    refine canonical_success _ ?_ ?_ ?_ ?_
    · simpa [d4] using hcanonical ⟨4, by decide⟩
    · simpa [d5] using hcanonical ⟨5, by decide⟩
    · simpa [d6] using hcanonical ⟨6, by decide⟩
    · simpa [d7] using hcanonical ⟨7, by decide⟩
  have hcm0 : field.CM31.new d0 d1 = .ok ⟨d0,d1⟩ := by
    simp [field.CM31.new]
  have hcm1 : field.CM31.new d2 d3 = .ok ⟨d2,d3⟩ := by
    simp [field.CM31.new]
  have hcm2 : field.CM31.new d4 d5 = .ok ⟨d4,d5⟩ := by
    simp [field.CM31.new]
  have hcm3 : field.CM31.new d6 d7 = .ok ⟨d6,d7⟩ := by
    simp [field.CM31.new]
  let value : CandidateWide := ⟨⟨⟨d0,d1⟩,⟨d2,d3⟩⟩,
                                 ⟨⟨d4,d5⟩,⟨d6,d7⟩⟩⟩
  refine ⟨value, ?_, ?_⟩
  · simp only [sampler.decode8, i0, i1, i2, i3, i4, i5, i6, i7,
      bind_tc_ok, hcm0, hcm1, hcm2, hcm3, hc0, hc1, field.WideExact.new,
      bind_tc_ok]
    rfl
  · simpa [value, d0,d1,d2,d3,d4,d5,d6,d7] using
      digitsField_candidate digits hcanonical

#print axioms decode8_candidate_eq_retained

end AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3
