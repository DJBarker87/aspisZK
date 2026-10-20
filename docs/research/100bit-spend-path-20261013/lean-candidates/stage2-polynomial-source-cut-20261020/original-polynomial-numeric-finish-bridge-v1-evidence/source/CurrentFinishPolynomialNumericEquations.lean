import CurrentFinishCandidateUnrolledPolynomialV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

/-- The actual seven parsed coefficients, in source Horner order, and decoded value. -/
def FinishPolynomialEvaluation (bytes : Slice U8) (alpha out : FinishE) : Prop :=
  ∃ coefficients : List E,
    (∀ c ∈ coefficients, CanonicalWide c) ∧
    List.Forall₂ (fun i c => currentRecordFieldLookupNat bytes i = .ok c)
      [6,5,4,3,2,1,0] coefficients ∧
    decodeFinish out = horner_value 0 (decodeFinish alpha) (coefficients.map decodeWide)

theorem finish_unrolled_polynomial_success_evaluation
    (bytes : Slice U8) (alpha out : FinishE) (ha : CanonicalFinish alpha)
    (h : finishUnrolledPolynomial bytes alpha = .ok out) :
    CanonicalFinish out ∧ FinishPolynomialEvaluation bytes alpha out := by
  unfold finishUnrolledPolynomial at h
  cases hc : current_unrolled_record_polynomial bytes (ofFinishE alpha) with
  | fail e => simp only [hc, bind_tc_fail] at h; cases h
  | div => simp only [hc, bind_tc_div] at h; cases h
  | ok result =>
    simp only [hc, bind_tc_ok] at h
    have hout : toFinishE result = out := Result.ok.inj h
    obtain ⟨Cresult, coefficients, Ccoefficients, hlookup, hvalue⟩ :=
      current_unrolled_record_polynomial_success bytes (ofFinishE alpha) result ha hc
    subst out
    refine ⟨?_,coefficients,Ccoefficients,hlookup,?_⟩
    · change CanonicalWide (ofFinishE (toFinishE result))
      rw [of_to_finish]
      exact Cresult
    · change decodeWide (ofFinishE (toFinishE result)) = _
      rw [of_to_finish]
      exact hvalue

theorem s2_unrolled_polynomial_numeric_equations {W D : Type}
    (ops : FinishOps W D) (v : AspisR1FinishRelationCurrent.verifier.View)
    (p : AspisR1FinishRelationCurrent.verifier.Prepared)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hv : p.variant = AspisR1FinishRelationCurrent.transport.Variant.S2)
    (hclaim : CanonicalFinish p.claim)
    (halpha0 : ∀ x, Array.index_usize p.alpha 0#usize = .ok x → CanonicalFinish x)
    (halpha1 : ∀ x, Array.index_usize p.alpha 1#usize = .ok x → CanonicalFinish x)
    (h : AspisR1FinishRelationCurrent.verifier.finish_relation
      (finishUnrolledPolynomialOps ops) v p a obs = .ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2 w sliced pair actual,
      Array.index_usize p.alpha 0#usize = .ok alpha0 ∧
      CanonicalFinish claim1 ∧ FinishPolynomialEvaluation v.round0 alpha0 claim1 ∧
      (∃ x0 x4, finishField v.round0 0#usize = .ok x0 ∧
        finishField v.round0 4#usize = .ok x4 ∧
        decodeFinish x0 + decodeFinish x4 = decodeFinish p.claim * (536870912 : AspisWideTower.WideExact)) ∧
      Array.index_usize p.alpha 1#usize = .ok alpha1 ∧
      CanonicalFinish claim2 ∧ FinishPolynomialEvaluation v.round1 alpha1 claim2 ∧
      (∃ x0 x4, finishField v.round1 0#usize = .ok x0 ∧
        finishField v.round1 4#usize = .ok x4 ∧
        decodeFinish x0 + decodeFinish x4 = decodeFinish claim1 * (536870912 : AspisWideTower.WideExact)) ∧
      (finishUnrolledPolynomialOps ops).newWeights p.variant p.semantic_alpha p.z = .ok (.Ok w) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice AspisR1FinishRelationCurrent.aspis_core.field.WideExact))
        p.alpha { «end» := 2#usize } = .ok sliced ∧
      (finishUnrolledPolynomialOps ops).pair w sliced v.final_message p.kappa = .ok (.Ok pair) ∧
      pair = claim2 ∧
      AspisR1FinishRelationCurrent.verifier.finish_query_dot (finishUnrolledPolynomialOps ops)
        v.final_message (alloc.vec.Vec.deref a.weights) = .ok (.Ok actual) ∧
      actual = a.rhs ∧ a.next = 22#usize := by
  let cop := finishUnrolledPolynomialOps ops
  have hfaith : ∀ x y, cop.eq x y = .ok true → x = y := by
    intro x y he
    exact finish_eq_success_true x y (by
      simpa [cop, finishUnrolledPolynomialOps, finishConcreteField,
        finishCheckedArithmetic, finishEq] using he)
  obtain ⟨alpha0,claim1,alpha1,claim2,w,sliced,pair,actual,
    h0,hrr0,h1,hrr1,hw,hs,hpair,hpairguard,_,hdot,hnext,hdotguard,_⟩ :=
    AspisR1FinishRelationCurrent.FinishCandidateOuterSuccess.s2_success_calls
      cop v p a obs hv h
  have hr0 := AspisR1FinishRelationCurrent.FinishCandidateEquations.round_equation
    cop hfaith v.round0 alpha0 p.claim claim1 0#usize hrr0
  have hr1 := AspisR1FinishRelationCurrent.FinishCandidateEquations.round_equation
    cop hfaith v.round1 alpha1 claim1 claim2 1#usize hrr1
  have hp1 : CanonicalFinish claim1 ∧ FinishPolynomialEvaluation v.round0 alpha0 claim1 := by
    rcases hr0 with ⟨_,_,_,_,_,_,_,_,_,_,_,hpoly⟩
    exact finish_unrolled_polynomial_success_evaluation v.round0 alpha0 claim1
      (halpha0 alpha0 h0) (by simpa [cop, finishUnrolledPolynomialOps] using hpoly)
  have hp2 : CanonicalFinish claim2 ∧ FinishPolynomialEvaluation v.round1 alpha1 claim2 := by
    rcases hr1 with ⟨_,_,_,_,_,_,_,_,_,_,_,hpoly⟩
    exact finish_unrolled_polynomial_success_evaluation v.round1 alpha1 claim2
      (halpha1 alpha1 h1) (by simpa [cop, finishUnrolledPolynomialOps] using hpoly)
  change AspisR1FinishRelationCurrent.FinishCandidateEquations.RoundEquation
    (finishArithmetic cop) v.round0 alpha0 p.claim claim1 at hr0
  change AspisR1FinishRelationCurrent.FinishCandidateEquations.RoundEquation
    (finishArithmetic cop) v.round1 alpha1 claim1 claim2 at hr1
  have guard0 := current_round_equation cop v.round0 alpha0 p.claim claim1 hclaim
    (finishField_success_canonical v.round0 0#usize)
    (finishField_success_canonical v.round0 4#usize) hr0
  have guard1 := current_round_equation cop v.round1 alpha1 claim1 claim2 hp1.1
    (finishField_success_canonical v.round1 0#usize)
    (finishField_success_canonical v.round1 4#usize) hr1
  refine ⟨alpha0,claim1,alpha1,claim2,w,sliced,pair,actual,h0,hp1.1,hp1.2,guard0,h1,hp2.1,hp2.2,guard1,hw,hs,hpair,?_,hdot,?_,?_⟩
  · exact AspisR1FinishRelationCurrent.FinishCandidateEquations.ne_guard_eq cop hfaith pair claim2 hpairguard
  · exact AspisR1FinishRelationCurrent.FinishCandidateEquations.ne_guard_eq cop hfaith actual a.rhs hdotguard
  · simpa only [bne_eq_false_iff_eq] using hnext

#print axioms finish_unrolled_polynomial_success_evaluation
#print axioms s2_unrolled_polynomial_numeric_equations
end AspisR1CurrentWide.Proof
