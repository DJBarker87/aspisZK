import S9PairSameLowCanonicalV1
import S9PairAfterLowFourTermCanonicalV1
import S9PairAfterTermsContV1
import S9PairSideZeroMulCallV1
import S9PairAddChainCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9PairSideZeroProductCanonicalV1

abbrev U := Std.Usize
abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev R := AspisR1S9PairCallerBodyPrefixV1.R
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- Same-run side-zero body evidence through the low-times-all product. The
low, terms, sums, and product all come from the one generated Pair body call;
only mapped successful-read canonicality contracts are premises. -/
theorem pair_body_sidezero_product_canonical
    (ap0 ap1 : Array PW (4#usize)) (extra : Array PQ (2#usize))
    (iterNext : R) (weights : Array PW (4#usize))
    (flow : ControlFlow (R × Array PW (4#usize)) (Array PW (4#usize)))
    (hbody : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
      ap0 ap1 extra 0#usize iterNext weights = .ok flow)
    (hap0 : ∀ (j : U) (x : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6W
          (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6W
          (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize
        (mapArray AspisR1S9CandidateHelperV1.toP6Q
          (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x)) :
    ∃ (q q1 q2 q3 unusedQ4 q4 q41 q8 q12 q16 : PQ)
      (low : PW) (t0 t1 t2 t3 : PW) (perm3 : U)
      (first2 first3 all product : PW) (out : Array PW (4#usize)),
      Array.index_usize extra 0#usize = .ok q ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul
        AspisR1S9PairCallerStepV1.field.QM31.ONE q = .ok q1 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q1 q = .ok q2 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q2 q = .ok q3 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q3 q = .ok unusedQ4 ∧
      Array.index_usize (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) 2#usize = .ok q4 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q4 = .ok q41 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q41 = .ok q8 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q8 q41 = .ok q12 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q8 = .ok q16 ∧
      AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
        (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) ap0 = .ok low ∧
      AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
        ap1 0#usize iterNext weights q41 q8 q12 q16 low = .ok flow ∧
      AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
        .ok (perm3,(t0,t1,t2,t3)) ∧
      AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
        ap1 0#usize iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 =
        .ok (.cont (iterNext, out)) ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add t0 t1 = .ok first2 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first2 t2 = .ok first3 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first3 t3 = .ok all ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low all = .ok product ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1S9PairCallerStepV1.toP6W low) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1S9PairCallerStepV1.toP6W all) := by
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail,hlowCan⟩ :=
    AspisR1S9PairSameLowCanonicalV1.same_pair_body_low_is_canonical
      ap0 ap1 extra 0#usize iterNext weights flow hbody (by decide) hap0 hap1 hextra
  obtain ⟨t0,t1,t2,t3,perm3,w0,w1,w2,w3,hterms,hperm3,hafterTerms,
      ht0,ht1,ht2,ht3,hpermWitness,ht0Can,ht1Can,ht2Can,ht3Can⟩ :=
    AspisR1S9PairAfterLowFourTermCanonicalV1.pair_after_low_four_terms_canonical
      ap1 0#usize iterNext weights q41 q8 q12 q16 low flow htail hap1
  obtain ⟨out,hflow⟩ := AspisR1S9PairAfterTermsContV1.pair_after_terms_success_cont
    ap1 iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 flow hafterTerms
  rw [hflow] at hafterTerms
  obtain ⟨first2,first3,all,product,hadd2,hadd3,haddAll,hmul⟩ :=
    AspisR1S9PairSideZeroMulCallV1.side_zero_tail_exposes_mul
      ap1 iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 out hafterTerms
  obtain ⟨hfirst2Can,hfirst3Can,hallCan⟩ :=
    AspisR1S9PairAddChainCanonicalV1.pair_four_term_adds_canonical
      t0 t1 t2 t3 first2 first3 all ht0Can ht1Can ht2Can ht3Can
      hadd2 hadd3 haddAll
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,t0,t1,t2,t3,perm3,
    first2,first3,all,product,out,hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,
    hlow,htail,hterms,hafterTerms,hadd2,hadd3,haddAll,hmul,hlowCan,hallCan⟩

#print axioms pair_body_sidezero_product_canonical

end AspisR1S9PairSideZeroProductCanonicalV1
