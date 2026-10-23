import S9PairCandidateAfterTermsMapV1
import S9PairMixedInputCanonicalV1
import S9PairTermPrefixMapV1
import S9PairTermChildrenV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedCallerReadbackV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize

private theorem bind_success_inv {α β : Type}
    (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Invert the fourth term prefix call to recover its same-run PERM/ap1/high
reads and mixed multiplication success. -/
theorem pair_term_prefix_last_call_children
    (ap1 : Array PW (4#usize)) (q41 q8 q12 : PQ)
    (perm3 : PU) (t0 t1 t2 t3 : PW)
    (h : AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
      .ok (perm3,(t0,t1,t2,t3))) :
    ∃ (x : PW) (a : PQ) (product : PW),
      Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM 3#usize =
        .ok perm3 ∧
      Array.index_usize ap1 perm3 = .ok x ∧
      Array.index_usize (Array.make 4#usize
        [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12]) 3#usize = .ok a ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x a = .ok product ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER = .ok t3 := by
  have hc := h
  unfold AspisR1S9PairTermPrefixMapV1.pairTermPrefix at hc
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12])
      0#usize) _ _ hc with ⟨r0,hr0,hc⟩
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12])
      1#usize) _ _ hc with ⟨r1,hr1,hc⟩
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12])
      2#usize) _ _ hc with ⟨r2,hr2,hc⟩
  rcases bind_success_inv
    (AspisR1S9PairTermPrefixMapV1.pairTermAt ap1
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12])
      3#usize) _ _ hc with ⟨r3,hr3,hc⟩
  have hlast := Result.ok.inj hc
  have hperm3 : r3.1 = perm3 := congrArg Prod.fst hlast
  have ht3 : r3.2 = t3 := congrArg (fun z : PU × (PW × PW × PW × PW) => z.2.2.2.2) hlast
  have hterm3 : AspisR1S9PairTermPrefixMapV1.pairTermAt ap1
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12])
      3#usize = .ok (perm3,t3) := by
    rw [← hperm3, ← ht3]
    exact hr3
  obtain ⟨x,a,product,hperm3,hread,hhigh,hmul,hm31⟩ :=
    AspisR1S9PairTermChildrenV1.pair_term_at_success_children ap1
      (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12])
      3#usize perm3 t3 hterm3
  exact ⟨x,a,product,hperm3,hread,hhigh,hmul,hm31⟩

/-- The fourth mixed product reached through a successful `pairAfterLow` call
is the exact same source-cut call after transporting canonicality from the
public mapped-ap1 read contract. -/
theorem pair_after_low_last_mixed_call_reflects_source
    (ap1 : Array PW (4#usize)) (side : PU)
    (iterNext : core.ops.range.Range Std.Usize)
    (weights : Array PW (4#usize)) (q41 q8 q12 q16 : PQ) (low : PW)
    (flow : ControlFlow (core.ops.range.Range Std.Usize × Array PW (4#usize))
      (Array PW (4#usize)))
    (hafter : AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
      ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow)
    (hap1 : ∀ (j : Std.Usize) (v : AspisR1S9HelperP6.field.WideExact),
      (Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v) →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∃ (t0 t1 t2 t3 : PW) (perm3 : PU) (x product : PW) (a : PQ)
      (sourceProduct : AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact),
      AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
        .ok (perm3,(t0,t1,t2,t3)) ∧
      Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM
        3#usize = .ok perm3 ∧
      Array.index_usize ap1 perm3 = .ok x ∧
      Array.index_usize (Array.make 4#usize
        [AspisR1S9PairCallerStepV1.field.QM31.ONE,q41,q8,q12]) 3#usize = .ok a ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x a = .ok product ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 product
        _root_.AspisR1S9PairCallerStepV1.weights.QUARTER = .ok t3 ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ a) = .ok sourceProduct ∧
      product = AspisR1S9PairMixedCallToSourceV1.srcToPairW sourceProduct ∧
      AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms ap1 side iterNext weights
        q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow := by
  obtain ⟨t0,t1,t2,t3,perm3,hprefix,hperm3,hafterTerms⟩ :=
    AspisR1S9PairCandidateAfterTermsMapV1.pair_after_low_terms_from_same_success
      ap1 side iterNext weights q41 q8 q12 q16 low flow hafter
  obtain ⟨x,a,product,hpermRead,hread,hhigh,hmul,hm31⟩ :=
    pair_term_prefix_last_call_children ap1 q41 q8 q12 perm3 t0 t1 t2 t3 hprefix
  obtain ⟨sourceProduct,hsource,hproduct⟩ :=
    AspisR1S9PairMixedInputCanonicalV1.pair_read_mixed_call_success_reflects_source
      ap1 perm3 x a product hread hap1 hmul
  exact ⟨t0,t1,t2,t3,perm3,x,product,a,sourceProduct,
    hprefix,hperm3,hread,hhigh,hmul,hm31,hsource,hproduct,hafterTerms⟩

#print axioms pair_after_low_last_mixed_call_reflects_source

end AspisR1S9PairMixedCallerReadbackV1
