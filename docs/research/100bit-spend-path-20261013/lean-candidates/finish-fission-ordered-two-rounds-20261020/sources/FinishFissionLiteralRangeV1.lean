import FinishFissionSourceSuccessJoinV3
import Aeneas.Std.RangeIter

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FinishFissionLiteralRange
open _root_.AspisR1FinishRelationCurrent
open AspisR1FinishFissionProof

abbrev Range := core.ops.range.Range Usize

private theorem forward_next_step (iter : Range) (hlt : iter.start.val < iter.end.val) :
    ∃ iter1 : Range,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter1) ∧
      iter1.start.val = iter.start.val + 1 ∧
      iter1.end = iter.end ∧
      iter.start.val + 1 ≤ Usize.max := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter hlt)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hstart, hend⟩
  cases hopt
  have hbound : iter.start.val + 1 ≤ Usize.max := by
    have hb : iter.start.val + 1 < 2 ^ System.Platform.numBits := by
      simpa [Usize.numBits, UScalarTy.numBits, hstart] using iter1.start.hBounds
    have hb' : iter.start.val + 1 ≤ 2 ^ System.Platform.numBits - 1 := by omega
    simpa [Usize.max, Usize.numBits, UScalarTy.numBits] using hb'
  exact ⟨iter1, hrun, hstart, hend, hbound⟩

private theorem forward_next_done (iter : Range) (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter) := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
      (partialOrdInst := core.cmp.PartialOrdUsize) (by intros; rfl) iter hge)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hiter⟩
  cases hopt
  cases hiter
  exact hrun

def range0 : Range := { start := 0#usize, «end» := 2#usize }
def range1 : Range := { start := 1#usize, «end» := 2#usize }
def range2 : Range := { start := 2#usize, «end» := 2#usize }

private def alpha0Entry (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[0]'(by
    have hlen : (0#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

private def alpha1Entry (p : verifier.Prepared) : aspis_core.field.WideExact :=
  p.alpha.val[1]'(by
    have hlen : (1#usize).val < (2#usize).val := by scalar_tac
    simpa [p.alpha.property] using hlen)

theorem next0 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range0 =
      .ok (some range0.start, range1) := by
  obtain ⟨iter1, hnext, hstart, hend, _⟩ :=
    forward_next_step range0 (by
      change (0#usize).val < (2#usize).val
      scalar_tac)
  have hs : iter1.start = 1#usize := by
    apply UScalar.eq_of_val_eq
    simpa [range0] using hstart
  have he : iter1.end = 2#usize := by simpa [range0] using hend
  have hr : iter1 = range1 := by
    cases iter1
    simp_all [range1, hs, he]
  rw [hr] at hnext
  exact hnext

theorem next1 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range1 =
      .ok (some range1.start, range2) := by
  obtain ⟨iter2, hnext, hstart, hend, _⟩ :=
    forward_next_step range1 (by
      change (1#usize).val < (2#usize).val
      scalar_tac)
  have hs : iter2.start = 2#usize := by
    apply UScalar.eq_of_val_eq
    simpa [range1] using hstart
  have he : iter2.end = 2#usize := by simpa [range1] using hend
  have hr : iter2 = range2 := by
    cases iter2
    simp_all [range2, hs, he]
  rw [hr] at hnext
  exact hnext

theorem next2 :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range2 =
      .ok (none, range2) := by
  exact forward_next_done range2 (by
    change (2#usize).val ≥ (2#usize).val
    exact le_rfl)

theorem s2_success_fission_model_no_range_hypotheses
    {W D : Type}
    (ops : FinishOps W D)
    (faithful : ∀ x y, ops.eq x y = .ok true → x = y)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (obs : Option (verifier.Phase → Result Unit))
    (hv : p.variant = transport.Variant.S2)
    (hfinish : verifier.finish_relation ops v p a obs = .ok (.Ok ())) :
    ∃ alpha0 claim1 alpha1 claim2,
      Array.index_usize p.alpha 0#usize = .ok alpha0 ∧
      Array.index_usize p.alpha 1#usize = .ok alpha1 ∧
      loopAdapter
        (fun vv pp claim round => AspisR1FinishFissionHelperAdapterV2.finishRoundAdapter ops vv pp claim round)
        (AspisR1FinishFissionSourceSuccessJoin.environmentOf v p) range0 p.claim = .ok (claim2, none) ∧
      FinishCandidateEquations.RoundEquation ops v.round0
        (alpha0Entry p) p.claim claim1 ∧
      FinishCandidateEquations.RoundEquation ops v.round1
        (alpha1Entry p) claim1 claim2 := by
  obtain ⟨alpha0, claim1, alpha1, claim2, hidx0, hidx1, hloop, heq0, heq1⟩ :=
    AspisR1FinishFissionSourceSuccessJoin.s2_success_fission_model
      ops faithful v p a obs hv hfinish range0 range1 range2
      (by rfl) (by rfl) next0 next1 next2
  exact ⟨alpha0, claim1, alpha1, claim2, hidx0, hidx1, hloop, heq0, heq1⟩

#print axioms next0
#print axioms next1
#print axioms next2
#print axioms s2_success_fission_model_no_range_hypotheses
end AspisR1FinishFissionLiteralRange
