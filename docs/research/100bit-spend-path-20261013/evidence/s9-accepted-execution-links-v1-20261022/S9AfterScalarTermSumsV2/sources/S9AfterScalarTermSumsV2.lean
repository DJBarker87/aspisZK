import S9AfterScalarTermSumsV1
import S9HighTermsTraceV1
import S9ConcreteArithmeticAcceptedRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9AfterScalarTermSumsV2

open AspisR1S9HelperP6

local instance concreteOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize
abbrev decW (x : field.WideExact) : AspisWideTower.WideExact :=
  AspisR1S9CurrentFieldOpsV1.decode x

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem successful_index_four {A : Type}
    (xs : Array A (4#usize)) (i : U) (x : A)
    (hi : i.val < 4)
    (h : Array.index_usize xs i = .ok x) :
    xs.val[i.val]'(by simpa [xs.property] using hi) = x := by
  obtain ⟨v,hv,hget⟩ := WP.spec_imp_exists
    (Array.index_usize_spec xs i (by simpa [xs.property] using hi))
  have heq : v = x := Result.ok.inj (hv.symm.trans h)
  have hx := heq.symm.trans hget
  exact hx.symm

/-- Same successful post-scalar body and the exact P6 high-term trace derive
the body’s three ordered sum meanings. No add-success or term-canonicality
premises are supplied: both are read from the body/trace and checked against
the concrete current WideExact addition semantics. -/
theorem after_scalar_success_terms_and_sums_mean
    (ap0 ap1 : W) (extra : Array Q (2#usize)) (side : U)
    (iterNext : core.ops.range.Range U) (weights0 : W)
    (q4 q8 q12 q16 : Q) (low : field.WideExact)
    (flow : ControlFlow (core.ops.range.Range U × W) W)
    (htail : @AspisR1S9TwoCallScalarMeaningV2.afterScalar
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low = .ok flow)
    (high : Array Q (4#usize))
    (hhighArray : high = Array.make 4#usize [field.QM31.ONE,q4,q8,q12])
    (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour ap1 high) :
    ∃ (terms : W) (state : (W × Array Q (4#usize)) × U)
      (we we1 first2 we2 first3 we3 all : field.WideExact),
      @core.array.from_fn field.WideExact weights.factored_s2_libra_weights.closure
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (4#usize)
        weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (ap1, high) = .ok (terms,state) ∧
      Array.index_usize terms 0#usize = .ok we ∧
      Array.index_usize terms 1#usize = .ok we1 ∧
      @field.WideExact.add concreteOps we we1 = .ok first2 ∧
      Array.index_usize terms 2#usize = .ok we2 ∧
      @field.WideExact.add concreteOps first2 we2 = .ok first3 ∧
      Array.index_usize terms 3#usize = .ok we3 ∧
      @field.WideExact.add concreteOps first3 we3 = .ok all ∧
      AspisR1S9CurrentFieldOpsV1.Canonical first2 ∧
      AspisR1S9CurrentFieldOpsV1.decode first2 =
        decW we + decW we1 ∧
      AspisR1S9CurrentFieldOpsV1.Canonical first3 ∧
      AspisR1S9CurrentFieldOpsV1.decode first3 =
        AspisR1S9CurrentFieldOpsV1.decode first2 + decW we2 ∧
      AspisR1S9CurrentFieldOpsV1.Canonical all ∧
      AspisR1S9CurrentFieldOpsV1.decode all =
        AspisR1S9CurrentFieldOpsV1.decode first3 + decW we3 ∧
      @AspisR1S9AfterScalarTermSumsV1.afterSums
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        ap1 side iterNext weights0 low first2 first3 all q4 q16 = .ok flow := by
  obtain ⟨termsBody,stateBody,we,we1,first2,we2,first3,we3,all,
      hfromfnBody,hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,hsuffix⟩ :=
    AspisR1S9AfterScalarTermSumsV1.after_scalar_success_terms_and_sums
      ap0 ap1 extra side iterNext weights0 q4 q8 q12 q16 low flow htail
  have hfromfnTrace := hterms.generated_from_fn
  rw [← hhighArray] at hfromfnBody
  have hpair := Result.ok.inj (hfromfnBody.symm.trans hfromfnTrace)
  have htermsEq : termsBody = hterms.terms := congrArg Prod.fst hpair
  subst termsBody
  have h4 : (4#usize).val = 4 := by decide
  have hbound0 : 0 < hterms.terms.val.length := by
    simpa [hterms.terms.property,h4] using (show 0 < 4 by decide)
  have hbound1 : 1 < hterms.terms.val.length := by
    simpa [hterms.terms.property,h4] using (show 1 < 4 by decide)
  have hbound2 : 2 < hterms.terms.val.length := by
    simpa [hterms.terms.property,h4] using (show 2 < 4 by decide)
  have hbound3 : 3 < hterms.terms.val.length := by
    simpa [hterms.terms.property,h4] using (show 3 < 4 by decide)
  have hwe0eq : we = hterms.call0.term := by
    have hcell := successful_index_four hterms.terms 0#usize we (by decide) hwe
    have hopt := (List.getElem?_eq_some_iff).mpr ⟨hbound0,hcell⟩
    rw [hterms.terms_values] at hopt
    exact Option.some.inj hopt.symm
  have hwe1eq : we1 = hterms.call1.term := by
    have hcell := successful_index_four hterms.terms 1#usize we1 (by decide) hwe1
    have hopt := (List.getElem?_eq_some_iff).mpr ⟨hbound1,hcell⟩
    rw [hterms.terms_values] at hopt
    exact Option.some.inj hopt.symm
  have hwe2eq : we2 = hterms.call2.term := by
    have hcell := successful_index_four hterms.terms 2#usize we2 (by decide) hwe2
    have hopt := (List.getElem?_eq_some_iff).mpr ⟨hbound2,hcell⟩
    rw [hterms.terms_values] at hopt
    exact Option.some.inj hopt.symm
  have hwe3eq : we3 = hterms.call3.term := by
    have hcell := successful_index_four hterms.terms 3#usize we3 (by decide) hwe3
    have hopt := (List.getElem?_eq_some_iff).mpr ⟨hbound3,hcell⟩
    rw [hterms.terms_values] at hopt
    exact Option.some.inj hopt.symm
  have hcan0 : AspisR1S9CurrentFieldOpsV1.Canonical we := by
    rw [hwe0eq]
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call0.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call0.term_canonical
  have hcan1 : AspisR1S9CurrentFieldOpsV1.Canonical we1 := by
    rw [hwe1eq]
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call1.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call1.term_canonical
  change @AspisR1S9HelperP6.FieldOps.wideAdd concreteOps we we1 = .ok first2 at hadd2
  have hsum2 := AspisR1.S9ConcreteArithmeticAcceptedRootV1.wideAdd_success
      we we1 first2 hcan0 hcan1 hadd2
  have hcan2 : AspisR1S9CurrentFieldOpsV1.Canonical we2 := by
    rw [hwe2eq]
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call2.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call2.term_canonical
  change @AspisR1S9HelperP6.FieldOps.wideAdd concreteOps first2 we2 = .ok first3 at hadd3
  have hsum3 := AspisR1.S9ConcreteArithmeticAcceptedRootV1.wideAdd_success
      first2 we2 first3 hsum2.1 hcan2 hadd3
  have hcan3 : AspisR1S9CurrentFieldOpsV1.Canonical we3 := by
    rw [hwe3eq]
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CurrentFieldOpsV1.toE hterms.call3.term)
    rw [AspisR1S9HighTermsConcreteV1.toE_eq_generated_toWide]
    exact hterms.call3.term_canonical
  change @AspisR1S9HelperP6.FieldOps.wideAdd concreteOps first3 we3 = .ok all at haddAll
  have hsumAll := AspisR1.S9ConcreteArithmeticAcceptedRootV1.wideAdd_success
      first3 we3 all hsum3.1 hcan3 haddAll
  exact ⟨hterms.terms,stateBody,we,we1,first2,we2,first3,we3,all,
    by simpa [hhighArray] using hfromfnBody,
    hwe,hwe1,hadd2,hwe2,hadd3,hwe3,haddAll,
    hsum2.1, hsum2.2,
    hsum3.1, hsum3.2,
    hsumAll.1, hsumAll.2, hsuffix⟩

#print axioms after_scalar_success_terms_and_sums_mean

end AspisR1S9AfterScalarTermSumsV2
