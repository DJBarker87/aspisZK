import S9CandidateArithmeticPrefixV1
import S9CandidateTermCallTotalityV1
import S9CandidateAfterTermsContTotalV1
import S9CandidateBodyPrefixV1
import S9CandidateBodyTermsV1
import S9CandidateBodyArrayBridgeV1
import S9CandidateActiveBodyAssemblerV1
import S9P6AfterTermsTotalV1
import S9HighTermsArrayCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateActiveBodyTotalityV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev PA := Array PW (4#usize)
abbrev CA := Array CW (4#usize)
abbrev MP := AspisR1S9CandidateTermStagesV1.MP
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem bind_ok {A B : Type} (m : Result A) (k : A → Result B)
    (x : A) (y : B) (hm : m = .ok x) (hk : k x = .ok y) :
    (do let a ← m; k a) = .ok y := by
  rw [hm]
  exact hk

private theorem generated_current_q (q : AspisR1S9HelperP6.field.QM31) :
    AspisR1S9GeneratedWideMulQM31V2.toQM q =
      AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM q := by
  cases q <;> rfl

private theorem qcanonical_to_p6
    (q : CQ)
    (h : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM
        (AspisR1S9CandidateHelperV1.toP6Q q))) :
    AspisR1S9P6AfterTermsTotalV1.CanonicalQ
      (AspisR1S9CandidateHelperV1.toP6Q q) := by
  change AspisR1CurrentWide.Proof.CanonicalQM
    (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
      (AspisR1S9CandidateHelperV1.toP6Q q))
  rw [← generated_current_q]
  exact h

/-- Construct the exact candidate active-body call from canonical source
reads. The selected P6 tail is totalized for the same callback terms, then its
checked full-Result map is inverted to recover the candidate suffix. -/
theorem candidate_active_body_total
    (ap0 ap1 : CA) (extra : Array CQ (2#usize)) (side : U)
    (iterNext : R) (weights : CA)
    (hside : side.val < 2)
    (hap0 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap0) j = .ok x →
      AspisR1S9CurrentFieldOpsV1.Canonical x)
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hextra : ∀ (j : U) (x : AspisR1S9HelperP6.field.QM31),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) j = .ok x →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM x))
    (hold : side ≠ 0#usize → ∀ x,
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W weights)
        1#usize = .ok x → AspisR1S9P6AfterTermsTotalV1.Canonical x) :
    ∃ (out : CA) (p6out : PA),
      AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
        ap0 ap1 extra side iterNext weights = .ok (.cont (iterNext,out)) ∧
      mapArray MP out = p6out ∧
      AspisR1S9P6AfterTermsTotalV1.Canonical
        (AspisR1S9P6AfterTermsTotalV1.cells p6out 1) := by
  obtain ⟨pfx⟩ := AspisR1S9CandidateArithmeticPrefixV1.candidate_arithmetic_prefix_total
    ap0 ap1 extra side hside hap0 hap1 hextra
  have htermsCan :=
    AspisR1S9HighTermsArrayCanonicalV1.high_terms_returned_array_reads_canonical
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q
        (AspisR1S9CandidateBodyTermsV1.candidateHigh pfx.q41 pfx.q8 pfx.q12))
      pfx.highTerms
  have hq41 : AspisR1S9P6AfterTermsTotalV1.CanonicalQ
      (AspisR1S9CandidateHelperV1.toP6Q pfx.q41) :=
    qcanonical_to_p6 pfx.q41 pfx.q41_canonical
  have hq16 : AspisR1S9P6AfterTermsTotalV1.CanonicalQ
      (AspisR1S9CandidateHelperV1.toP6Q pfx.q16) :=
    qcanonical_to_p6 pfx.q16 pfx.q16_canonical
  obtain ⟨p6out,hp6tail,hp6can1⟩ :=
    AspisR1S9P6AfterTermsTotalV1.p6_after_terms_total
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) pfx.highTerms.terms
      side iterNext (mapArray AspisR1S9CandidateHelperV1.toP6W weights)
      (AspisR1S9CandidateHelperV1.toP6W pfx.low)
      (AspisR1S9CandidateHelperV1.toP6Q pfx.q41)
      (AspisR1S9CandidateHelperV1.toP6Q pfx.q16)
      hap1 htermsCan pfx.low_canonical hq41 hq16 hold
  obtain ⟨c0,c1,c2,c3,h0,h1,h2,h3⟩ :=
    AspisR1S9CandidateTermCallTotalityV1.candidate_four_term_calls_total_of_high_terms
      ap1 pfx.q41 pfx.q8 pfx.q12 pfx.highTerms
  have htermsArrayVals :=
    AspisR1S9CandidateBodyArrayBridgeV1.candidate_term_array_maps_to_high_terms
      ap1 (AspisR1S9CandidateBodyTermsV1.candidateHigh pfx.q41 pfx.q8 pfx.q12)
      c0 c1 c2 c3 pfx.highTerms
  have htermsArray : mapArray AspisR1S9CandidateHelperV1.toP6W
      (AspisR1S9CandidateBodyTermsV1.candidateTerms c0.term c1.term c2.term c3.term) =
      pfx.highTerms.terms := by
    apply Subtype.ext
    exact htermsArrayVals
  have hp6candidate := hp6tail
  rw [← htermsArray] at hp6candidate
  obtain ⟨cout,hcandidateTail,hmapOut⟩ :=
    AspisR1S9CandidateAfterTermsContTotalV1.candidate_after_terms_cont_total_of_p6_success
      ap1 weights iterNext side pfx.q41 pfx.q8 pfx.q12 pfx.q16 pfx.low
      c3.perm c3.permRead c0.term c1.term c2.term c3.term p6out hp6candidate
  have hrest : AspisR1S9CandidateBodyPrefixV1.candidateAfterLow
      ap1 side iterNext weights pfx.q41 pfx.q8 pfx.q12 pfx.q16 pfx.low =
      .ok (.cont (iterNext,cout)) := by
    unfold AspisR1S9CandidateBodyPrefixV1.candidateAfterLow
    have hcoef0 : Array.index_usize
        (Array.make 4#usize [field.QM31.ONE,pfx.q41,pfx.q8,pfx.q12]) 0#usize =
          .ok c0.coefficient := c0.coefficientRead
    have hcoef1 : Array.index_usize
        (Array.make 4#usize [field.QM31.ONE,pfx.q41,pfx.q8,pfx.q12]) 1#usize =
          .ok c1.coefficient := c1.coefficientRead
    have hcoef2 : Array.index_usize
        (Array.make 4#usize [field.QM31.ONE,pfx.q41,pfx.q8,pfx.q12]) 2#usize =
          .ok c2.coefficient := c2.coefficientRead
    have hcoef3 : Array.index_usize
        (Array.make 4#usize [field.QM31.ONE,pfx.q41,pfx.q8,pfx.q12]) 3#usize =
          .ok c3.coefficient := c3.coefficientRead
    refine bind_ok _ _ _ _ c0.permRead ?_
    refine bind_ok _ _ _ _ c0.inputRead ?_
    refine bind_ok _ _ _ _ hcoef0 ?_
    refine bind_ok _ _ _ _ c0.wideMulCall ?_
    refine bind_ok _ _ _ _ c0.scalarMulCall ?_
    refine bind_ok _ _ _ _ c1.permRead ?_
    refine bind_ok _ _ _ _ c1.inputRead ?_
    refine bind_ok _ _ _ _ hcoef1 ?_
    refine bind_ok _ _ _ _ c1.wideMulCall ?_
    refine bind_ok _ _ _ _ c1.scalarMulCall ?_
    refine bind_ok _ _ _ _ c2.permRead ?_
    refine bind_ok _ _ _ _ c2.inputRead ?_
    refine bind_ok _ _ _ _ hcoef2 ?_
    refine bind_ok _ _ _ _ c2.wideMulCall ?_
    refine bind_ok _ _ _ _ c2.scalarMulCall ?_
    refine bind_ok _ _ _ _ c3.permRead ?_
    refine bind_ok _ _ _ _ c3.inputRead ?_
    refine bind_ok _ _ _ _ hcoef3 ?_
    refine bind_ok _ _ _ _ c3.wideMulCall ?_
    refine bind_ok _ _ _ _ c3.scalarMulCall ?_
    exact hcandidateTail
  have hbody : AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
      ap0 ap1 extra side iterNext weights = .ok (.cont (iterNext,cout)) := by
    unfold AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
    simp only [pfx.seed_read,pfx.mul1,pfx.mul2,pfx.mul3,pfx.mul4,pfx.q4_read,
      pfx.square41,pfx.square8,pfx.mul12,pfx.square16,pfx.scalar,bind_tc_ok,hrest]
  exact ⟨cout,p6out,hbody,hmapOut,hp6can1⟩

#print axioms candidate_active_body_total

end AspisR1S9CandidateActiveBodyTotalityV1
