import S9CandidateBodyEvidenceV1
import S9CandidateHelperOperationBridgeV1
import S3S9ConcreteSquareSemanticsV1
import S9ConcreteQMMulAcceptedRootV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateHighArraySemanticsV1

open AspisR1S9CandidateBodyEvidenceV1
open AspisR1S9CandidateBodyPrefixV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateHelperBridgeV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev Q4 := Array CQ (4#usize)
abbrev P6Q4 := Array PQ (4#usize)
abbrev CanonicalP6 (q : PQ) := AspisR1CurrentWide.Proof.CanonicalQM
  (AspisR1S9GeneratedWideMulQM31V2.toQM q)
abbrev DecodeP6 (q : PQ) := AspisR1CurrentWide.Proof.decodeQM
  (AspisR1S9GeneratedWideMulQM31V2.toQM q)

private theorem generated_to_current (x : PQ) :
    AspisR1S9GeneratedWideMulQM31V2.toQM x =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x := by
  cases x <;> rfl

private theorem candidate_toP6_one :
    AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE =
      AspisR1S9HelperP6.field.QM31.ONE := by
  unfold AspisR1S9CandidateHelperV1.toP6Q
    AspisR1S9CandidateHelperV1.toP6CM AspisR1S9CandidateHelperV1.toP6M
    AspisR1S9CandidateHelperV1.field.QM31.ONE AspisR1S9HelperP6.field.QM31.ONE
  rfl

private theorem candidate_mul_concrete
    (x y z : CQ)
    (h : AspisR1S9CandidateHelperV1.field.QM31.mul x y = .ok z) :
    @AspisR1S9HelperP6.FieldOps.qmMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q x)
      (AspisR1S9CandidateHelperV1.toP6Q y) =
      .ok (AspisR1S9CandidateHelperV1.toP6Q z) := by
  have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_mul x y
  rw [h] at hm
  simpa [AspisR1S9CandidateHelperBridgeV1.mapResult] using hm.symm

private theorem candidate_square_concrete
    (x z : CQ)
    (h : AspisR1S9CandidateHelperV1.field.QM31.square x = .ok z) :
    @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q x) =
      .ok (AspisR1S9CandidateHelperV1.toP6Q z) := by
  have hs := AspisR1S9CandidateHelperBridgeV1.map_qm_square x
  rw [h] at hs
  simpa [AspisR1S9CandidateHelperBridgeV1.mapResult] using hs.symm

private theorem make4_index_two {α : Type} (a b c d : α) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := by
  unfold Array.index_usize
  simp [Array.make]

private theorem index_success_bound {A : Type} {N : Std.Usize}
    (a : Array A N) (i : Std.Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

private theorem usize_eq_of_val_eq (a b : Std.Usize) (h : a.val = b.val) :
    a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UScalar.val] at h
      have hab := BitVec.eq_of_toNat_eq h
      subst bv
      rfl

private theorem one_canonical : CanonicalP6 AspisR1S9HelperP6.field.QM31.ONE := by
  change @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
    AspisR1S9HelperP6.field.QM31.ONE
  exact @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.one_canonical
    AspisR1CurrentWide.Proof.ExactQM _
    AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
    AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics

private theorem candidate_mul_semantics
    (x y z : CQ) (hx : CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q x))
    (hy : CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q y))
    (hmul : AspisR1S9CandidateHelperV1.field.QM31.mul x y = .ok z) :
    CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q z) ∧
      DecodeP6 (AspisR1S9CandidateHelperV1.toP6Q z) =
        DecodeP6 (AspisR1S9CandidateHelperV1.toP6Q x) *
        DecodeP6 (AspisR1S9CandidateHelperV1.toP6Q y) := by
  exact AspisR1.S9ConcreteQMMulAcceptedRootV1.qmMul_success
    (AspisR1S9CandidateHelperV1.toP6Q x)
    (AspisR1S9CandidateHelperV1.toP6Q y)
    (AspisR1S9CandidateHelperV1.toP6Q z) hx hy
    (candidate_mul_concrete x y z hmul)

private theorem candidate_square_semantics
    (x z : CQ) (hx : CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q x))
    (hsquare : AspisR1S9CandidateHelperV1.field.QM31.square x = .ok z) :
    CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q z) ∧
      DecodeP6 (AspisR1S9CandidateHelperV1.toP6Q z) =
        DecodeP6 (AspisR1S9CandidateHelperV1.toP6Q x) *
        DecodeP6 (AspisR1S9CandidateHelperV1.toP6Q x) := by
  have hxCurrent : @AspisR1S9HelperP6PowerSemanticsV1.QMSemantics.canonical
      AspisR1CurrentWide.Proof.ExactQM _
      AspisR1S9HelperP6PowerSemanticsV1.currentFieldOps
      AspisR1S9HelperP6PowerSemanticsV1.currentQMSemantics
      (AspisR1S9CandidateHelperV1.toP6Q x) := by
    dsimp only [CanonicalP6] at hx
    rw [generated_to_current] at hx
    exact hx
  obtain ⟨out, hsq, hcan, hdecode⟩ :=
    AspisR1S9ConcreteSquareSemanticsV1.concrete_qmSquare_total
      (AspisR1S9CandidateHelperV1.toP6Q x) hxCurrent
  have hactual := candidate_square_concrete x z hsquare
  have hout : out = AspisR1S9CandidateHelperV1.toP6Q z :=
    Result.ok.inj (hsq.symm.trans hactual)
  subst out
  constructor
  · dsimp only [CanonicalP6]
    rw [generated_to_current]
    exact hcan
  · dsimp only [DecodeP6]
    rw [generated_to_current, generated_to_current]
    exact hdecode

/-- Canonicality of every coefficient in the candidate high array is derived
from the exact successful child operations in the same candidate body. The
only external semantic input is canonicality of that body's selected seed. -/
theorem candidate_high_array_canonical
    (q q1 q2 q3 q4 q41 q8 q12 : CQ)
    (hseed : CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q q))
    (hmul1 : AspisR1S9CandidateHelperV1.field.QM31.mul
      AspisR1S9CandidateHelperV1.field.QM31.ONE q = .ok q1)
    (hmul2 : AspisR1S9CandidateHelperV1.field.QM31.mul q1 q = .ok q2)
    (hmul3 : AspisR1S9CandidateHelperV1.field.QM31.mul q2 q = .ok q3)
    (hread4 : Array.index_usize
      (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3])
      2#usize = .ok q4)
    (hsq41 : AspisR1S9CandidateHelperV1.field.QM31.square q4 = .ok q41)
    (hsq8 : AspisR1S9CandidateHelperV1.field.QM31.square q41 = .ok q8)
    (hmul12 : AspisR1S9CandidateHelperV1.field.QM31.mul q8 q41 = .ok q12) :
    ∀ (j : Std.Usize) (z : PQ),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12)) j = .ok z →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM z) := by
  have hOneCandidate : CanonicalP6
      (AspisR1S9CandidateHelperV1.toP6Q
        AspisR1S9CandidateHelperV1.field.QM31.ONE) := by
    rw [candidate_toP6_one]
    exact one_canonical
  have hq1 := candidate_mul_semantics
    AspisR1S9CandidateHelperV1.field.QM31.ONE q q1 hOneCandidate hseed hmul1
  have hq2 := candidate_mul_semantics q1 q q2 hq1.1 hseed hmul2
  have hq3 := candidate_mul_semantics q2 q q3 hq2.1 hseed hmul3
  have hq4eq : q4 = q2 := by
    have hstd := make4_index_two
      AspisR1S9CandidateHelperV1.field.QM31.ONE q1 q2 q3
    exact Result.ok.inj (hread4.symm.trans hstd)
  have hq4can : CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q q4) := by
    rw [hq4eq]
    exact hq2.1
  have hq41 := candidate_square_semantics q4 q41 hq4can hsq41
  have hq8 := candidate_square_semantics q41 q8 hq41.1 hsq8
  have hq12 := candidate_mul_semantics q8 q41 q12 hq8.1 hq41.1 hmul12
  have hOne : CanonicalP6 AspisR1S9HelperP6.field.QM31.ONE := one_canonical
  have hOneMap : AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE =
      AspisR1S9HelperP6.field.QM31.ONE := candidate_toP6_one
  have hfour : (4#usize).val = 4 := by decide
  intro j z hread
  have hjbound := index_success_bound
    (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12)) j z hread
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hjcases with hj | hj | hj | hj
  · have heq : j = 0#usize := usize_eq_of_val_eq j 0#usize (by simpa using hj)
    subst j
    have hentry : Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12))
        0#usize = .ok AspisR1S9HelperP6.field.QM31.ONE := by
      have hsrc : Array.index_usize (candidateHigh q41 q8 q12) 0#usize =
          .ok AspisR1S9CandidateHelperV1.field.QM31.ONE := by
        simp [candidateHigh, Array.index_usize, Array.make]
      have hm := mapArray_index_result AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12) 0#usize
      rw [hsrc] at hm
      simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult, candidate_toP6_one] using hm.symm
    have hz : z = AspisR1S9HelperP6.field.QM31.ONE :=
      (Result.ok.inj (hentry.symm.trans hread)).symm
    simpa [hz] using hOne
  · have heq : j = 1#usize := usize_eq_of_val_eq j 1#usize (by simpa using hj)
    subst j
    have hentry : Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12))
        1#usize = .ok (AspisR1S9CandidateHelperV1.toP6Q q41) := by
      have hsrc : Array.index_usize (candidateHigh q41 q8 q12) 1#usize = .ok q41 := by
        simp [candidateHigh, Array.index_usize, Array.make]
      have hm := mapArray_index_result AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12) 1#usize
      rw [hsrc] at hm
      simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
    have hz : z = AspisR1S9CandidateHelperV1.toP6Q q41 :=
      (Result.ok.inj (hentry.symm.trans hread)).symm
    simpa [hz] using hq41.1
  · have heq : j = 2#usize := usize_eq_of_val_eq j 2#usize (by simpa using hj)
    subst j
    have hentry : Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12))
        2#usize = .ok (AspisR1S9CandidateHelperV1.toP6Q q8) := by
      have hsrc : Array.index_usize (candidateHigh q41 q8 q12) 2#usize = .ok q8 := by
        simp [candidateHigh, Array.index_usize, Array.make]
      have hm := mapArray_index_result AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12) 2#usize
      rw [hsrc] at hm
      simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
    have hz : z = AspisR1S9CandidateHelperV1.toP6Q q8 :=
      (Result.ok.inj (hentry.symm.trans hread)).symm
    simpa [hz] using hq8.1
  · have heq : j = 3#usize := usize_eq_of_val_eq j 3#usize (by simpa using hj)
    subst j
    have hentry : Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12))
        3#usize = .ok (AspisR1S9CandidateHelperV1.toP6Q q12) := by
      have hsrc : Array.index_usize (candidateHigh q41 q8 q12) 3#usize = .ok q12 := by
        simp [candidateHigh, Array.index_usize, Array.make]
      have hm := mapArray_index_result AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12) 3#usize
      rw [hsrc] at hm
      simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
    have hz : z = AspisR1S9CandidateHelperV1.toP6Q q12 :=
      (Result.ok.inj (hentry.symm.trans hread)).symm
    simpa [hz] using hq12.1

#print axioms candidate_high_array_canonical

end AspisR1S9CandidateHighArraySemanticsV1
