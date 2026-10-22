import S9CandidateBodyPrefixMapV1
import S9FactoredLoopBodyShapeV3
import S9CandidateBodyArrayBridgeV1
import S9CandidateHelperOperationBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateActiveBodyAssemblerV1

open AspisR1S9CandidateBodyPrefixMapV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateBodyEvidenceV1
open AspisR1S9CandidateBodyArrayBridgeV1
open AspisR1S9CandidateFoldMapPrimitivesV1
open AspisR1S9CandidateHelperV1
open AspisR1S9HelperP6
open AspisR1S9FactoredLoopBodyShapeV3

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CArray := Array CW (4#usize)
abbrev PArray := Array PW (4#usize)

private theorem make4_index_two {α : Type} (a b c d : α) :
    Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = .ok c := by
  unfold Array.index_usize
  simp [Array.make]

/-- Exact P6 tail beginning after the generated four-term array. The tail
remains an explicit continuation in the assembler theorem, so its success is
proved by the side-specific tail transport rather than postulated as a child
operation law. -/
def p6AfterTerms [AspisR1S9HelperP6.FieldOps]
    (ap1 : PArray) (terms : PArray) (side : U) (iterNext : R)
    (weights : PArray) (low : PW) (q4 q16 : PQ) : Result (ControlFlow (R × PArray) PArray) := do
  let we ← Array.index_usize terms 0#usize
  let we1 ← Array.index_usize terms 1#usize
  let first2 ← field.WideExact.add we we1
  let we2 ← Array.index_usize terms 2#usize
  let first3 ← field.WideExact.add first2 we2
  let we3 ← Array.index_usize terms 3#usize
  let all ← field.WideExact.add first3 we3
  if side = 0#usize then do
    let we4 ← field.WideExact.mul low all
    let weights1 ← Array.update weights 0#usize we4
    let we5 ← field.WideExact.mul low first3
    let we6 ← field.WideExact.mul_qm31 we5 q16
    let a ← Array.update weights1 1#usize we6
    ok (cont (iterNext, a))
  else do
    let we4 ← Array.index_usize weights 1#usize
    let i ← Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize
    let we5 ← Array.index_usize ap1 i
    let we6 ← field.WideExact.mul_m31 we5 _root_.AspisR1S9HelperP6.weights.QUARTER
    let we7 ← field.WideExact.mul low we6
    let we8 ← field.WideExact.add we4 we7
    let weights1 ← Array.update weights 1#usize we8
    let we9 ← field.WideExact.mul low all
    let we10 ← field.WideExact.mul_qm31 we9 q4
    let weights2 ← Array.update weights1 2#usize we10
    let we11 ← field.WideExact.mul low first2
    let q3 ← field.QM31.mul q16 q4
    let we12 ← field.WideExact.mul_qm31 we11 q3
    let a ← Array.update weights2 3#usize we12
    ok (cont (iterNext, a))

/-- The exact mapped prefix of the actual candidate `body` is the prefix of
the retained P6 `activeBody`. The endpoint is the P6 post-`from_fn` tail
expression with the same mapped values and same returned term array. -/
theorem candidate_body_prefix_assembles_p6
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize))
    (iter iterNext : R) (side : U) (weights : CArray)
    (flow : ControlFlow (R × CArray) CArray)
    (p6flow : ControlFlow (R × PArray) PArray)
    (hprefix : CandidateBodyPrefixEvidence ap0 ap1 extra iter iterNext side weights flow)
    (hsuffix : ∀ (q41 q8 q12 q16 : CQ) (low : CW) (perm3 : U)
      (t0 t1 t2 t3 : CW),
      Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3 →
      candidateAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low perm3
        t0 t1 t2 t3 = .ok flow →
      @p6AfterTerms AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
        (mapArray AspisR1S9CandidateHelperV1.toP6W
          (candidateTerms t0 t1 t2 t3)) side iterNext
        (mapArray AspisR1S9CandidateHelperV1.toP6W weights)
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
        (AspisR1S9CandidateHelperV1.toP6Q q16) = .ok p6flow) :
    @AspisR1S9FactoredLoopBodyShapeV3.activeBody
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
        (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
        side iterNext (mapArray AspisR1S9CandidateHelperV1.toP6W weights) =
      .ok p6flow := by
  rcases hprefix with ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
    c0,c1,c2,c3,p6Values,hterms,hq,hkp,hvals,hq1,hq2,hq3,hunused,
    hq4,hq41,hq8,hq12,hq16,hlow,htail,htermsArray,hlowP6⟩
  have hpowArray : mapArray AspisR1S9CandidateHelperV1.toP6Q
      (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) =
      p6Values := by
    apply Subtype.ext
    change [AspisR1S9CandidateHelperV1.toP6Q
        AspisR1S9CandidateHelperV1.field.QM31.ONE,
      AspisR1S9CandidateHelperV1.toP6Q q1,
      AspisR1S9CandidateHelperV1.toP6Q q2,
      AspisR1S9CandidateHelperV1.toP6Q q3] = p6Values.val
    exact hvals.symm
  have hcq4 : q4 = q2 := by
    have hm := make4_index_two
      AspisR1S9CandidateHelperV1.field.QM31.ONE q1 q2 q3
    exact Result.ok.inj (hq4.symm.trans hm)
  have hpq2 : Array.index_usize p6Values 2#usize =
      .ok (AspisR1S9CandidateHelperV1.toP6Q q2) := by
    rw [← hpowArray]
    have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9CandidateHelperV1.toP6Q
      (Array.make 4#usize
        [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) 2#usize
    rw [make4_index_two AspisR1S9CandidateHelperV1.field.QM31.ONE q1 q2 q3] at hm
    simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
  have hkpConcrete : @AspisR1S9HelperP6.weights.kpowers
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
      (AspisR1S9CandidateHelperV1.toP6Q q) = .ok p6Values := by
    rw [AspisR1S9ConcreteFieldOpsV1.kpowers_concrete_eq_current]
    exact hkp
  have hqP6 : Array.index_usize
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) side =
      .ok (AspisR1S9CandidateHelperV1.toP6Q q) := by
    have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
      AspisR1S9CandidateHelperV1.toP6Q extra side
    rw [hq] at hm
    simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm.symm
  have hq41Map : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q q2) =
      .ok (AspisR1S9CandidateHelperV1.toP6Q q41) := by
    have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_square q4
    rw [hq41] at hm
    simpa [AspisR1S9CandidateHelperBridgeV1.mapResult, hcq4] using hm.symm
  have hq8Map : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q q41) =
      .ok (AspisR1S9CandidateHelperV1.toP6Q q8) := by
    have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_square q41
    rw [hq8] at hm
    simpa [AspisR1S9CandidateHelperBridgeV1.mapResult] using hm.symm
  have hq12Map : @AspisR1S9HelperP6.FieldOps.qmMul
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q q8)
      (AspisR1S9CandidateHelperV1.toP6Q q41) =
      .ok (AspisR1S9CandidateHelperV1.toP6Q q12) := by
    have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_mul q8 q41
    rw [hq12] at hm
    simpa [AspisR1S9CandidateHelperBridgeV1.mapResult] using hm.symm
  have hq16Map : @AspisR1S9HelperP6.FieldOps.qmSquare
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9CandidateHelperV1.toP6Q q8) =
      .ok (AspisR1S9CandidateHelperV1.toP6Q q16) := by
    have hm := AspisR1S9CandidateHelperBridgeV1.map_qm_square q8
    rw [hq16] at hm
    simpa [AspisR1S9CandidateHelperBridgeV1.mapResult] using hm.symm
  have hhigh : mapArray AspisR1S9CandidateHelperV1.toP6Q
      (AspisR1S9CandidateBodyTermsV1.candidateHigh q41 q8 q12) =
      Array.make 4#usize [AspisR1S9HelperP6.field.QM31.ONE,
        AspisR1S9CandidateHelperV1.toP6Q q41,
        AspisR1S9CandidateHelperV1.toP6Q q8,
        AspisR1S9CandidateHelperV1.toP6Q q12] := by
    apply Subtype.ext
    exact AspisR1S9CandidateBodyArrayBridgeV1.map_candidate_high_array
      q41 q8 q12 (AspisR1S9CandidateHelperV1.toP6Q q41)
      (AspisR1S9CandidateHelperV1.toP6Q q8)
      (AspisR1S9CandidateHelperV1.toP6Q q12) rfl rfl rfl
  let generated : (PArray × Array PQ (4#usize)) → Prop := fun st =>
    AspisR1S9HelperP6.core.array.from_fn 4#usize
      _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      st =
      .ok (hterms.terms,(st,4#usize))
  have hstate :
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1,
        mapArray AspisR1S9CandidateHelperV1.toP6Q
          (AspisR1S9CandidateBodyTermsV1.candidateHigh q41 q8 q12)) =
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1,
        Array.make 4#usize [AspisR1S9HelperP6.field.QM31.ONE,
          AspisR1S9CandidateHelperV1.toP6Q q41,
          AspisR1S9CandidateHelperV1.toP6Q q8,
          AspisR1S9CandidateHelperV1.toP6Q q12]) :=
    Prod.ext rfl hhigh
  have hgenerated := congrArg generated hstate
  have htermsP6 : generated
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1,
        Array.make 4#usize [AspisR1S9HelperP6.field.QM31.ONE,
          AspisR1S9CandidateHelperV1.toP6Q q41,
          AspisR1S9CandidateHelperV1.toP6Q q8,
          AspisR1S9CandidateHelperV1.toP6Q q12]) :=
    hgenerated.mp hterms.generated_from_fn
  change AspisR1S9HelperP6.core.array.from_fn 4#usize
      _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
      ((mapArray AspisR1S9CandidateHelperV1.toP6W ap1),
        Array.make 4#usize [AspisR1S9HelperP6.field.QM31.ONE,
          AspisR1S9CandidateHelperV1.toP6Q q41,
          AspisR1S9CandidateHelperV1.toP6Q q8,
          AspisR1S9CandidateHelperV1.toP6Q q12]) =
    .ok (hterms.terms,
      ((mapArray AspisR1S9CandidateHelperV1.toP6W ap1,
        Array.make 4#usize [AspisR1S9HelperP6.field.QM31.ONE,
          AspisR1S9CandidateHelperV1.toP6Q q41,
          AspisR1S9CandidateHelperV1.toP6Q q8,
          AspisR1S9CandidateHelperV1.toP6Q q12]),4#usize)) at htermsP6
  have htermsArrayEq : mapArray AspisR1S9CandidateHelperV1.toP6W
      (candidateTerms c0.term c1.term c2.term c3.term) = hterms.terms := by
    apply Subtype.ext
    exact htermsArray
  have htailMapped := hsuffix q41 q8 q12 q16 low c3.perm
    c0.term c1.term c2.term c3.term c3.permRead htail
  rw [htermsArrayEq] at htailMapped
  unfold AspisR1S9FactoredLoopBodyShapeV3.activeBody
  unfold _root_.AspisR1S9HelperP6.field.QM31.square
    _root_.AspisR1S9HelperP6.field.QM31.mul
  simp only [hqP6, hkpConcrete, hpq2, hq41Map, hq8Map, hq12Map,
    hq16Map, hlowP6, htermsP6, bind_tc_ok]
  unfold p6AfterTerms at htailMapped
  exact htailMapped

end AspisR1S9CandidateActiveBodyAssemblerV1

#print axioms AspisR1S9CandidateActiveBodyAssemblerV1.candidate_body_prefix_assembles_p6
