import S9CandidateBodyTermsV1
import S9HighTermsTraceV1
import S9CandidateHelperOperationBridgeV1
import S9CandidateFoldMapPrimitivesV1
import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateBodyArrayBridgeV1

open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateHelperV1
open AspisR1S9HelperP6
open AspisR1S9HighTermsTraceV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev U := Std.Usize
abbrev W4 := Array CW (4#usize)
abbrev Q4 := Array CQ (4#usize)

private theorem candidate_toP6_one :
    AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE =
        AspisR1S9HelperP6.field.QM31.ONE := by
  unfold AspisR1S9CandidateHelperV1.toP6Q
    AspisR1S9CandidateHelperV1.toP6CM
    AspisR1S9CandidateHelperV1.toP6M
    AspisR1S9CandidateHelperV1.field.QM31.ONE
    AspisR1S9HelperP6.field.QM31.ONE
  rfl

private theorem candidate_quarter_toP6 :
    AspisR1S9CandidateHelperV1.toP6M
      AspisR1S9CandidateHelperV1.weights.QUARTER =
        AspisR1S9HelperP6.weights.QUARTER := by
  unfold AspisR1S9CandidateHelperV1.toP6M
    AspisR1S9CandidateHelperV1.weights.QUARTER
    AspisR1S9HelperP6.weights.QUARTER
  rfl

/-- A candidate high array is mapped pointwise to the exact P6 high array for
the same square/multiply child outputs. -/
theorem map_candidate_high_array
    (q41 q8 q12 : CQ) (p4 p8 p12 : PQ)
    (h41 : AspisR1S9CandidateHelperV1.toP6Q q41 = p4)
    (h8 : AspisR1S9CandidateHelperV1.toP6Q q8 = p8)
    (h12 : AspisR1S9CandidateHelperV1.toP6Q q12 = p12) :
    (mapArray AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12)).val =
      (Array.make 4#usize [AspisR1S9HelperP6.field.QM31.ONE,p4,p8,p12]).val := by
  change [AspisR1S9CandidateHelperV1.toP6Q
      AspisR1S9CandidateHelperV1.field.QM31.ONE,
    AspisR1S9CandidateHelperV1.toP6Q q41,
    AspisR1S9CandidateHelperV1.toP6Q q8,
    AspisR1S9CandidateHelperV1.toP6Q q12] =
    [AspisR1S9HelperP6.field.QM31.ONE,p4,p8,p12]
  rw [candidate_toP6_one, h41, h8, h12]

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Invert the exact retained P6 callback body to recover its two concrete
wide multiplication child results. -/
private theorem p6_callback_child_calls
    (ap1 : Array PW (4#usize)) (high : Array PQ (4#usize))
    (i : U) (call : AspisR1S9HighTermsConcreteV1.HighTermCall ap1 high i) :
    ∃ mid,
      @FieldOps.wideMulQM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        call.x call.q = .ok mid ∧
      @FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        mid AspisR1S9HelperP6.weights.QUARTER = .ok call.term := by
  have hcur := call.callback_success
  change (do
      let permutation ← Array.index_usize AspisR1S9HelperP6.weights.PERM i
      let xv ← Array.index_usize ap1 permutation
      let qv ← Array.index_usize high i
      let product ← @FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps xv qv
      let value ← @FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        product AspisR1S9HelperP6.weights.QUARTER
      .ok (value, (ap1, high))) = .ok (call.term, (ap1, high)) at hcur
  rcases bind_success_inv
      (Array.index_usize AspisR1S9HelperP6.weights.PERM i) _ _ hcur with
    ⟨perm,hperm,hcur⟩
  have hperm_eq : perm = call.perm := Result.ok.inj (hperm.symm.trans call.perm_read)
  subst perm
  rcases bind_success_inv (Array.index_usize ap1 call.perm) _ _ hcur with
    ⟨x,hx,hcur⟩
  have hx_eq : x = call.x := Result.ok.inj (hx.symm.trans call.ap1_read)
  subst x
  rcases bind_success_inv (Array.index_usize high i) _ _ hcur with
    ⟨q,hq,hcur⟩
  have hq_eq : q = call.q := Result.ok.inj (hq.symm.trans call.high_read)
  subst q
  rcases bind_success_inv
      (@FieldOps.wideMulQM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps call.x call.q)
      _ _ hcur with ⟨mid,hmid,hcur⟩
  rcases bind_success_inv
      (@FieldOps.wideMulM31 AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        mid AspisR1S9HelperP6.weights.QUARTER) _ _ hcur with
    ⟨term,hterm,hcur⟩
  have hresult := Result.ok.inj hcur
  have htermEq : term = call.term := congrArg Prod.fst hresult
  subst term
  exact ⟨mid,hmid,hterm⟩

/-- The same explicit candidate term call, transported through the checked
operation map, equals the corresponding actual callback result in the retained
P6 `HighTermsFour`. Array reads are aligned by the carrier-mapped arrays. -/
theorem candidate_term_maps_to_p6_call
    (ap1 : W4) (high : Q4) (i : U)
    (candidateCall : CandidateTermCall ap1 high i)
    (p6Call : AspisR1S9HighTermsConcreteV1.HighTermCall
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q high) i) :
    AspisR1S9CandidateHelperV1.toP6W candidateCall.term = p6Call.term := by
  have hpermEq : candidateCall.perm = p6Call.perm := by
    have hpermdef : AspisR1S9CandidateHelperV1.weights.PERM =
        AspisR1S9HelperP6.weights.PERM := by
      unfold AspisR1S9CandidateHelperV1.weights.PERM AspisR1S9HelperP6.weights.PERM
      rfl
    have hcandidateOnP6 : Array.index_usize AspisR1S9HelperP6.weights.PERM i =
        .ok candidateCall.perm := by
      rw [← hpermdef]
      exact candidateCall.permRead
    exact Result.ok.inj (hcandidateOnP6.symm.trans p6Call.perm_read)
  have hinputEq : AspisR1S9CandidateHelperV1.toP6W candidateCall.input =
      p6Call.x := by
    have hmap := mapArray_index_result AspisR1S9CandidateHelperV1.toP6W
      ap1 candidateCall.perm
    rw [candidateCall.inputRead] at hmap
    simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hmap
    have hp6 := p6Call.ap1_read
    rw [← hpermEq] at hp6
    exact Result.ok.inj (hmap.trans hp6)
  have hcoefEq : AspisR1S9CandidateHelperV1.toP6Q candidateCall.coefficient =
      p6Call.q := by
    have hmap := mapArray_index_result AspisR1S9CandidateHelperV1.toP6Q
      high i
    rw [candidateCall.coefficientRead] at hmap
    simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hmap
    exact Result.ok.inj (hmap.trans p6Call.high_read)
  obtain ⟨p6Product,hp6Mul,hp6Scale⟩ :=
    p6_callback_child_calls
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q high) i p6Call
  have hproduct : AspisR1S9CandidateHelperV1.toP6W candidateCall.product =
      p6Product := by
    have hmap := AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31
      candidateCall.input candidateCall.coefficient
    rw [candidateCall.wideMulCall] at hmap
    rw [hinputEq, hcoefEq] at hmap
    simp only [AspisR1S9CandidateHelperBridgeV1.mapResult] at hmap
    exact Result.ok.inj (hmap.trans hp6Mul)
  have hmap := AspisR1S9CandidateHelperBridgeV1.map_wide_mul_m31
    candidateCall.product AspisR1S9CandidateHelperV1.weights.QUARTER
  rw [candidateCall.scalarMulCall] at hmap
  rw [hproduct, candidate_quarter_toP6] at hmap
  simp only [AspisR1S9CandidateHelperBridgeV1.mapResult] at hmap
  exact Result.ok.inj (hmap.trans hp6Scale)

/-- The array of explicit candidate term results maps elementwise to the exact
four terms constructed by the retained P6 callback trace. The per-slot inputs
are the actual success witnesses inverted from the candidate continuation. -/
theorem candidate_term_array_maps_to_high_terms
    (ap1 : W4) (high : Q4)
    (c0 : CandidateTermCall ap1 high 0#usize)
    (c1 : CandidateTermCall ap1 high 1#usize)
    (c2 : CandidateTermCall ap1 high 2#usize)
    (c3 : CandidateTermCall ap1 high 3#usize)
    (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q high)) :
    (mapArray AspisR1S9CandidateHelperV1.toP6W
      (candidateTerms c0.term c1.term c2.term c3.term)).val = hterms.terms.val := by
  have h0 := candidate_term_maps_to_p6_call ap1 high 0#usize c0 hterms.call0
  have h1 := candidate_term_maps_to_p6_call ap1 high 1#usize c1 hterms.call1
  have h2 := candidate_term_maps_to_p6_call ap1 high 2#usize c2 hterms.call2
  have h3 := candidate_term_maps_to_p6_call ap1 high 3#usize c3 hterms.call3
  change [AspisR1S9CandidateHelperV1.toP6W c0.term,
      AspisR1S9CandidateHelperV1.toP6W c1.term,
      AspisR1S9CandidateHelperV1.toP6W c2.term,
      AspisR1S9CandidateHelperV1.toP6W c3.term] = hterms.terms.val
  rw [hterms.terms_values, h0, h1, h2, h3]

#print axioms map_candidate_high_array
#print axioms candidate_term_maps_to_p6_call
#print axioms candidate_term_array_maps_to_high_terms

end AspisR1S9CandidateBodyArrayBridgeV1
