import S9PairSideOneCallV1
import S9PairFourTermCanonicalV1
import S9PairAddChainCanonicalV1
import S9PairMixedInputCanonicalV1
import S9PairQuarterTermCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairSideOneOperandsCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize
abbrev PR := AspisR1S9PairCallerBodyPrefixV1.R
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev PairArray := Array PW (4#usize)

/-- The exact side-one tail's ordered sums and quarter-scaled same-run read
are canonical when the four callback terms and mapped `ap1` reads are
canonical. Both the additions and the quarter operation are the calls exposed
by the successful source suffix. -/
theorem side_one_operands_canonical
    (ap1 : PairArray) (iterNext : PR) (weights : PairArray)
    (q41 q8 q12 q16 : PQ) (low : PW) (perm3 : PU)
    (t0 t1 t2 t3 : PW)
    (flow : ControlFlow (PR × PairArray) PairArray)
    (htail : AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
      ap1 1#usize iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow)
    (hterms : AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
      .ok (perm3,(t0,t1,t2,t3)))
    (hap1 : ∀ (j : PU) (v : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∃ (output : PairArray) (first2 first3 all quarter : PW),
      flow = .cont (iterNext, output) ∧
      Canonical (AspisR1S9PairCallerStepV1.toP6W first2) ∧
      Canonical (AspisR1S9PairCallerStepV1.toP6W first3) ∧
      Canonical (AspisR1S9PairCallerStepV1.toP6W all) ∧
      AspisR1S9HighTermsTraceV1.canonicalW
        (AspisR1S9PairCallerStepV1.toP6W quarter) := by
  obtain ⟨output, first2, first3, all, old1, ap1perm, quarter, weighted, sum1,
      weights1, allProduct, allScaled, weights2, first2Product, first2Scaled, q10,
      h2, h3, hAll, _hold1, hread, hquarter, _hweighted, _hsum1, _hweights1,
      _hallProduct, _hallScaled, _hweights2, _hfirst2Product, _hq10,
      _hfirst2Scaled, hflow, _houtput⟩ :=
    AspisR1S9PairSideOneCallV1.side_one_tail_exposes_calls
      ap1 iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 flow htail
  obtain ⟨_w0, _w1, _w2, _w3, _ht0, _ht1, _ht2, _ht3, _hperm3,
      ht0Can, ht1Can, ht2Can, ht3Can⟩ :=
    AspisR1S9PairFourTermCanonicalV1.pair_term_prefix_four_terms_canonical
      ap1 q41 q8 q12 perm3 t0 t1 t2 t3 hterms hap1
  obtain ⟨hfirst2Can, hfirst3Can, hallCan⟩ :=
    AspisR1S9PairAddChainCanonicalV1.pair_four_term_adds_canonical
      t0 t1 t2 t3 first2 first3 all ht0Can ht1Can ht2Can ht3Can h2 h3 hAll
  have hap1permCan := AspisR1S9PairMixedInputCanonicalV1.pair_read_current_canonical
    ap1 perm3 ap1perm hread hap1
  have hquarterCan := AspisR1S9PairQuarterTermCanonicalV1.pair_quarter_term_success_canonical
    ap1perm quarter hap1permCan hquarter
  exact ⟨output, first2, first3, all, quarter, hflow,
    hfirst2Can, hfirst3Can, hallCan, hquarterCan⟩

#print axioms side_one_operands_canonical

end AspisR1S9PairSideOneOperandsCanonicalV1
