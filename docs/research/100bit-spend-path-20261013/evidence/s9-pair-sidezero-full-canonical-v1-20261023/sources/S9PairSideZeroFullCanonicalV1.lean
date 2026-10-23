import S9PairSideZeroProductCanonicalV1
import S9PairSideZeroFullCallsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9PairSideZeroFullCanonicalV1

abbrev U := Std.Usize
abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev R := AspisR1S9PairCallerBodyPrefixV1.R
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- From one successful side-zero Pair body call, retain its exact low, term
sums, both low-times-sum products, mixed result, writes and final output.
Canonicality of the low and final sum is derived by the existing same-call
prefix and term proofs. -/
theorem pair_body_sidezero_full_calls_canonical
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
      (first2 first3 all productAll productFirst3 mixed : PW)
      (weights1 : Array PW (4#usize)) (out : Array PW (4#usize)),
      Array.index_usize extra 0#usize = .ok q ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul
        AspisR1S9PairCallerStepV1.field.QM31.ONE q = .ok q1 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q1 q = .ok q2 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q2 q = .ok q3 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q3 q = .ok unusedQ4 ∧
      Array.index_usize
        (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3])
        2#usize = .ok q4 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q4 = .ok q41 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q41 = .ok q8 ∧
      AspisR1S9PairCallerStepV1.field.QM31.mul q8 q41 = .ok q12 ∧
      AspisR1S9PairCallerStepV1.field.QM31.square q8 = .ok q16 ∧
      AspisR1S9PairCallerStepV1.weights.Weights.scalar_factor
        (Array.make 4#usize [AspisR1S9PairCallerStepV1.field.QM31.ONE,q1,q2,q3]) ap0 = .ok low ∧
      AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
        .ok (perm3,(t0,t1,t2,t3)) ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add t0 t1 = .ok first2 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first2 t2 = .ok first3 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.add first3 t3 = .ok all ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low all = .ok productAll ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul low first3 = .ok productFirst3 ∧
      AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 productFirst3 q16 = .ok mixed ∧
      Array.update weights 0#usize productAll = .ok weights1 ∧
      Array.update weights1 1#usize mixed = .ok out ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1S9PairCallerStepV1.toP6W low) ∧
      AspisR1S9CurrentFieldOpsV1.Canonical (AspisR1S9PairCallerStepV1.toP6W all) := by
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,t0,t1,t2,t3,perm3,
      first2,first3,all,productAll0,out,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,hafterLow,
      hprefix,hafterTerms,hadd2,hadd3,haddAll,hmulAll0,hlowCan,hallCan⟩ :=
    AspisR1S9PairSideZeroProductCanonicalV1.pair_body_sidezero_product_canonical
      ap0 ap1 extra iterNext weights flow hbody hap0 hap1 hextra
  obtain ⟨first2',first3',all',productAll,productFirst3,mixed,weights1,
      hadd2',hadd3',haddAll',hmulAll,hupdate0,hmulFirst3,hmixed,hupdate1⟩ :=
    AspisR1S9PairSideZeroFullCallsV1.side_zero_tail_exposes_full_calls
      ap1 iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 out hafterTerms
  have heq2 : first2' = first2 := Result.ok.inj (hadd2'.symm.trans hadd2)
  rw [heq2] at hadd3'
  have heq3 : first3' = first3 := Result.ok.inj (hadd3'.symm.trans hadd3)
  rw [heq3] at haddAll'
  have heqAll : all' = all := Result.ok.inj (haddAll'.symm.trans haddAll)
  rw [heqAll] at hmulAll
  have heqProduct : productAll = productAll0 :=
    Result.ok.inj (hmulAll.symm.trans hmulAll0)
  subst first2'
  subst first3'
  subst all'
  subst productAll0
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,t0,t1,t2,t3,perm3,
    first2,first3,all,productAll,productFirst3,mixed,weights1,out,
    hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,hprefix,
    hadd2',hadd3',haddAll',hmulAll,hmulFirst3,hmixed,hupdate0,hupdate1,
    hlowCan,hallCan⟩

#print axioms pair_body_sidezero_full_calls_canonical

end AspisR1S9PairSideZeroFullCanonicalV1
