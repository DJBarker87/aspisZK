import S9PairSideOneOutputCanonicalV1
import S9PairCandidateAfterTermsMapV1
import S9PairArrayUpdateCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairSideOneFullArrayCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize
abbrev PR := AspisR1S9PairCallerBodyPrefixV1.R
abbrev PairArray := Array PW (4#usize)
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev P6MapW := AspisR1S9CandidateHelperV1.toP6W
abbrev PairP6W := AspisR1S9PairCallerStepV1.toP6W
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- The actual side-one suffix preserves canonicality of every successful
mapped output read. The same successful `pairAfterLow` execution supplies
the four term calls and its residual suffix; the three writes then preserve
the mapped-read invariant at every bounded slot. -/
theorem side_one_after_low_full_array_canonical
    (ap1 : PairArray) (iterNext : PR) (weights : PairArray)
    (q41 q8 q12 q16 : PQ) (low : PW)
    (flow : ControlFlow (PR × PairArray) PairArray)
    (hafter : AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
      ap1 1#usize iterNext weights q41 q8 q12 q16 low = .ok flow)
    (hap1 : ∀ (j : PU) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v)
    (hweights : ∀ (j : PU) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW weights)) j = .ok v →
      Canonical v)
    (hlow : Canonical (PairP6W low)) :
    ∃ (output : PairArray),
      flow = .cont (iterNext, output) ∧
      (∀ (j : PU) (v : P6W),
        Array.index_usize (mapArray P6MapW (mapArray PairMapW output)) j = .ok v →
        Canonical v) := by
  obtain ⟨t0, t1, t2, t3, perm3, hterms, _hperm3, htail⟩ :=
    AspisR1S9PairCandidateAfterTermsMapV1.pair_after_low_terms_from_same_success
      ap1 1#usize iterNext weights q41 q8 q12 q16 low flow hafter
  obtain ⟨output, sum1, allScaled, first2Scaled, weights1, weights2,
      hflow, hupdate1, hupdate2, hupdate3,
      hsum1, hallScaled, hfirst2Scaled⟩ :=
    AspisR1S9PairSideOneOutputCanonicalV1.side_one_output_values_canonical
      ap1 iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 flow
      htail hterms hap1 hweights hlow
  have hsum1' : Canonical (P6MapW (PairMapW sum1)) := by
    change Canonical (AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW sum1))
    rw [AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW]
    exact hsum1
  have hallScaled' : Canonical (P6MapW (PairMapW allScaled)) := by
    change Canonical (AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW allScaled))
    rw [AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW]
    exact hallScaled
  have hfirst2Scaled' : Canonical (P6MapW (PairMapW first2Scaled)) := by
    change Canonical (AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW first2Scaled))
    rw [AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW]
    exact hfirst2Scaled
  have hcan1 := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_nested_canonical_reads
    PairMapW P6MapW Canonical weights 1#usize sum1 weights1 (by decide)
    hupdate1 hweights hsum1'
  have hcan2 := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_nested_canonical_reads
    PairMapW P6MapW Canonical weights1 2#usize allScaled weights2 (by decide)
    hupdate2 hcan1 hallScaled'
  have hcan3 := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_nested_canonical_reads
    PairMapW P6MapW Canonical weights2 3#usize first2Scaled output (by decide)
    hupdate3 hcan2 hfirst2Scaled'
  exact ⟨output, hflow, hcan3⟩

#print axioms side_one_after_low_full_array_canonical

end AspisR1S9PairSideOneFullArrayCanonicalV1
