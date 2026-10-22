import S9CandidateBodyArrayBridgeV1
import S9CandidateHelperOperationBridgeV1
import S9CandidateFoldMapPrimitivesV1
import S9HighTermsTraceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateTermCallTotalityV1

open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev U := Std.Usize
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PQ := AspisR1S9HelperP6.field.QM31
abbrev W4 := Array CW (4#usize)
abbrev Q4 := Array CQ (4#usize)
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem mapResult_ok_inv {A B : Type} (f : A → B) (r : Result A) (b : B)
    (hmap : AspisR1S9CandidateHelperBridgeV1.mapResult f r = .ok b) :
    ∃ a, r = .ok a ∧ f a = b := by
  cases r with
  | ok a => exact ⟨a, rfl, Result.ok.inj hmap⟩
  | fail e => simp [AspisR1S9CandidateHelperBridgeV1.mapResult] at hmap
  | div => simp [AspisR1S9CandidateHelperBridgeV1.mapResult] at hmap

private theorem helper_mapResult_eq_fold_mapResult {A B : Type}
    (f : A → B) (r : Result A) :
    AspisR1S9CandidateHelperBridgeV1.mapResult f r =
      AspisR1S9CandidateFoldMapPrimitivesV1.mapResult f r := by
  cases r <;> rfl

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem p6_callback_child_calls
    (ap1 : Array PW (4#usize)) (high : Array PQ (4#usize))
    (i : U) (call : AspisR1S9HighTermsConcreteV1.HighTermCall ap1 high i) :
    ∃ mid,
      @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps call.x call.q = .ok mid ∧
      @AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps mid
        AspisR1S9HelperP6.weights.QUARTER = .ok call.term := by
  have hcur := call.callback_success
  change (do
      let permutation ← Array.index_usize AspisR1S9HelperP6.weights.PERM i
      let xv ← Array.index_usize ap1 permutation
      let qv ← Array.index_usize high i
      let product ← @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps xv qv
      let value ← @AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps product
        AspisR1S9HelperP6.weights.QUARTER
      .ok (value, (ap1, high))) = .ok (call.term, (ap1, high)) at hcur
  rcases bind_success_inv
      (Array.index_usize AspisR1S9HelperP6.weights.PERM i) _ _ hcur with
    ⟨perm,hperm,hcur⟩
  have hpermEq : perm = call.perm := Result.ok.inj (hperm.symm.trans call.perm_read)
  subst perm
  rcases bind_success_inv (Array.index_usize ap1 call.perm) _ _ hcur with
    ⟨x,hx,hcur⟩
  have hxEq : x = call.x := Result.ok.inj (hx.symm.trans call.ap1_read)
  subst x
  rcases bind_success_inv (Array.index_usize high i) _ _ hcur with
    ⟨q,hq,hcur⟩
  have hqEq : q = call.q := Result.ok.inj (hq.symm.trans call.high_read)
  subst q
  rcases bind_success_inv
      (@AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps call.x call.q) _ _ hcur with
    ⟨mid,hmid,hcur⟩
  rcases bind_success_inv
      (@AspisR1S9HelperP6.FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps mid
        AspisR1S9HelperP6.weights.QUARTER) _ _ hcur with
    ⟨term,hterm,hcur⟩
  have hresult := Result.ok.inj hcur
  have htermEq : term = call.term := congrArg Prod.fst hresult
  subst term
  exact ⟨mid,hmid,hterm⟩

/-- Build the actual candidate `CandidateTermCall` from one successful
selected P6 callback at the same index. Every candidate arithmetic child is
obtained by inversion of an existing full-Result operation-map equality;
there is no candidate-call-success premise. -/
theorem candidate_term_call_total_of_p6_call
    (ap1 : W4) (q41 q8 q12 : CQ) (i : U)
    (p6Call : AspisR1S9HighTermsConcreteV1.HighTermCall
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12)) i) :
    Nonempty {c : CandidateTermCall ap1 (candidateHigh q41 q8 q12) i //
      AspisR1S9CandidateHelperV1.toP6W c.term = p6Call.term} := by
  let cHigh := candidateHigh q41 q8 q12
  have hpermDef : AspisR1S9CandidateHelperV1.weights.PERM =
      AspisR1S9HelperP6.weights.PERM := by
    unfold AspisR1S9CandidateHelperV1.weights.PERM AspisR1S9HelperP6.weights.PERM
    rfl
  have hpermRead : Array.index_usize AspisR1S9CandidateHelperV1.weights.PERM i =
      .ok p6Call.perm := by
    rw [hpermDef]
    exact p6Call.perm_read
  have hinputMap : AspisR1S9CandidateHelperBridgeV1.mapResult
      AspisR1S9CandidateHelperV1.toP6W (Array.index_usize ap1 p6Call.perm) =
      .ok p6Call.x := by
    have h := mapArray_index_result AspisR1S9CandidateHelperV1.toP6W ap1 p6Call.perm
    rw [← helper_mapResult_eq_fold_mapResult] at h
    exact h.trans p6Call.ap1_read
  obtain ⟨input,hinputRead,hinputEq⟩ := mapResult_ok_inv
      AspisR1S9CandidateHelperV1.toP6W (Array.index_usize ap1 p6Call.perm) p6Call.x hinputMap
  have hhighMap : AspisR1S9CandidateHelperBridgeV1.mapResult
      AspisR1S9CandidateHelperV1.toP6Q (Array.index_usize cHigh i) =
      .ok p6Call.q := by
    have h := mapArray_index_result AspisR1S9CandidateHelperV1.toP6Q cHigh i
    rw [← helper_mapResult_eq_fold_mapResult] at h
    exact h.trans p6Call.high_read
  obtain ⟨coefficient,hcoefficientRead,hcoefficientEq⟩ := mapResult_ok_inv
      AspisR1S9CandidateHelperV1.toP6Q (Array.index_usize cHigh i) p6Call.q hhighMap
  obtain ⟨mid,hp6Mul,hp6Scale⟩ := p6_callback_child_calls
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
    (mapArray AspisR1S9CandidateHelperV1.toP6Q cHigh) i p6Call
  have hcandidateMulMap : AspisR1S9CandidateHelperBridgeV1.mapResult
      AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 input coefficient) =
      .ok mid := by
    rw [AspisR1S9CandidateHelperBridgeV1.map_wide_mul_qm31]
    rw [hinputEq,hcoefficientEq]
    exact hp6Mul
  obtain ⟨product,hproductCall,hproductEq⟩ := mapResult_ok_inv
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul_qm31 input coefficient)
    mid hcandidateMulMap
  have hquarter : AspisR1S9CandidateHelperV1.toP6M
      AspisR1S9CandidateHelperV1.weights.QUARTER =
      AspisR1S9HelperP6.weights.QUARTER := by
    unfold AspisR1S9CandidateHelperV1.toP6M
      AspisR1S9CandidateHelperV1.weights.QUARTER AspisR1S9HelperP6.weights.QUARTER
    rfl
  have hcandidateScaleMap : AspisR1S9CandidateHelperBridgeV1.mapResult
      AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 product
        AspisR1S9CandidateHelperV1.weights.QUARTER) = .ok p6Call.term := by
    rw [AspisR1S9CandidateHelperBridgeV1.map_wide_mul_m31,hproductEq,hquarter]
    exact hp6Scale
  obtain ⟨term,htermCall,htermEq⟩ := mapResult_ok_inv
    AspisR1S9CandidateHelperV1.toP6W
    (AspisR1S9CandidateHelperV1.field.WideExact.mul_m31 product
      AspisR1S9CandidateHelperV1.weights.QUARTER) p6Call.term hcandidateScaleMap
  exact ⟨⟨{
    term := term
    perm := p6Call.perm
    input := input
    coefficient := coefficient
    product := product
    permRead := hpermRead
    inputRead := hinputRead
    coefficientRead := hcoefficientRead
    wideMulCall := hproductCall
    scalarMulCall := htermCall
  }, htermEq⟩⟩

/-- All four candidate callback-shaped term calls are constructible from the
four actual calls in one retained P6 `HighTermsFour` witness. Each result is
for the matching index and the same mapped `ap1`/candidate high arrays. -/
theorem candidate_four_term_calls_total_of_high_terms
    (ap1 : W4) (q41 q8 q12 : CQ)
    (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q (candidateHigh q41 q8 q12))) :
    ∃ (c0 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 0#usize)
      (c1 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 1#usize)
      (c2 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 2#usize)
      (c3 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 3#usize),
      AspisR1S9CandidateHelperV1.toP6W c0.term = hterms.call0.term ∧
      AspisR1S9CandidateHelperV1.toP6W c1.term = hterms.call1.term ∧
      AspisR1S9CandidateHelperV1.toP6W c2.term = hterms.call2.term ∧
      AspisR1S9CandidateHelperV1.toP6W c3.term = hterms.call3.term := by
  obtain ⟨⟨c0,h0⟩⟩ := candidate_term_call_total_of_p6_call ap1 q41 q8 q12
    0#usize hterms.call0
  obtain ⟨⟨c1,h1⟩⟩ := candidate_term_call_total_of_p6_call ap1 q41 q8 q12
    1#usize hterms.call1
  obtain ⟨⟨c2,h2⟩⟩ := candidate_term_call_total_of_p6_call ap1 q41 q8 q12
    2#usize hterms.call2
  obtain ⟨⟨c3,h3⟩⟩ := candidate_term_call_total_of_p6_call ap1 q41 q8 q12
    3#usize hterms.call3
  exact ⟨c0,c1,c2,c3,h0,h1,h2,h3⟩

#print axioms candidate_term_call_total_of_p6_call
#print axioms candidate_four_term_calls_total_of_high_terms

end AspisR1S9CandidateTermCallTotalityV1
