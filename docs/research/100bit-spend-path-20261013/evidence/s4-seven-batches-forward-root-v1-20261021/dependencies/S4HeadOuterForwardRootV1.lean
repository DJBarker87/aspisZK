import S4HeadBatchBodyForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadOuterForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cell)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt)
open AspisR1FastDotsCurrentHeadTermForwardRootV1 (install)
open AspisR1FastDotsLimbFoldForwardRootV1 (limbCap)
open AspisR1FastDotsHeadBatchBodyForwardRootV1 (StepBy BatchBody batch_body_forward)
abbrev OuterLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0

theorem outer_loop_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : StepBy) (limbs : Array Std.U64 8#usize) (b : Nat)
    (hs : iter.iter.start.val≤26) (he : iter.iter.end=26#usize) (hstep : iter.step_by=4#usize)
    (hbudget : b+8*((26-iter.iter.start.val+3)/4)≤64)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparsed : ∀ term : Usize, term.val<26 → ParsedAt a g slot term)
    (hinput : ∀ j : Fin 8, cell limbs j≤b*limbCap) :
    ∃ out : Array Std.U64 8#usize,
      OuterLoop (install base) iter a g slot limbs = .ok out ∧
      (∀ j : Fin 8, cell out j≤(b+8*((26-iter.iter.start.val+3)/4))*limbCap) := by
  induction hm : (26-iter.iter.start.val+3)/4 using Nat.strong_induction_on generalizing iter limbs b with
  | h m ih =>
    have hpos : iter.step_by.val>0 := by rw [hstep]; decide
    obtain ⟨⟨opt,iter'⟩,hn,hpost⟩ := WP.spec_imp_exists
      (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpos)
    by_cases hi : iter.iter.start.val<26
    · have hit : iter.iter.start.val < iter.iter.end.val := by rw [he]; exact hi
      simp only [hit,↓reduceIte] at hpost
      have hn' : core.iter.adapters.step_by.IteratorStepBy.next
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some iter.iter.start,iter') := by simpa only [hpost.1.1] using hn
      have hv : iter'.iter.start.val= min (iter.iter.start.val+4) 26 := by
        simpa [hstep,he] using hpost.1.2
      have he' : iter'.iter.end=26#usize := hpost.2.1.trans he
      have hstep' : iter'.step_by=4#usize := hpost.2.2.trans hstep
      have hm' : (26-iter'.iter.start.val+3)/4+1=m := by
        by_cases hadd : iter.iter.start.val+4≤26
        · rw [Nat.min_eq_left hadd] at hv
          omega
        · rw [Nat.min_eq_right (by omega)] at hv
          omega
      obtain ⟨updated,hb,hbnd⟩ := batch_body_forward base a g slot iter.iter.start
        iter iter' limbs b hn' hi (by omega) hcoords hparsed hinput
      obtain ⟨out,hl,hout⟩ := ih ((26-iter'.iter.start.val+3)/4) (by omega)
        iter' updated (b+8) (by omega) he' hstep' (by omega) hbnd rfl
      refine ⟨out,?_,?_⟩
      · change loop (fun st : StepBy × Array Std.U64 8#usize =>
          BatchBody (install base) a g slot st.1 st.2) (iter',updated)=.ok out at hl
        change loop (fun st : StepBy × Array Std.U64 8#usize =>
          BatchBody (install base) a g slot st.1 st.2) (iter,limbs)=.ok out
        rw [loop.eq_def]
        simpa only [hb,bind_tc_ok] using hl
      · have hbndEq : b+8*m=(b+8)+8*((26-iter'.iter.start.val+3)/4) := by omega
        rw [hbndEq]
        exact hout
    · have hit : ¬ (iter.iter.start.val < iter.iter.end.val) := by rw [he]; exact hi
      simp only [hit,↓reduceIte] at hpost
      have hn' : core.iter.adapters.step_by.IteratorStepBy.next
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (none,iter') := by simpa only [hpost.1.1] using hn
      have hb : BatchBody (install base) a g slot iter limbs=.ok (.done limbs) := by
        simp [BatchBody,
          AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body,hn']
      refine ⟨limbs,?_,?_⟩
      · change loop (fun st : StepBy × Array Std.U64 8#usize =>
          BatchBody (install base) a g slot st.1 st.2) (iter,limbs)=.ok limbs
        rw [loop.eq_def]
        simpa only [hb,bind_tc_ok]
      · have hm0 : m=0 := by omega
        rw [hm0,Nat.mul_zero,Nat.add_zero]
        exact hinput

#print axioms outer_loop_forward
end AspisR1FastDotsHeadOuterForwardRootV1
