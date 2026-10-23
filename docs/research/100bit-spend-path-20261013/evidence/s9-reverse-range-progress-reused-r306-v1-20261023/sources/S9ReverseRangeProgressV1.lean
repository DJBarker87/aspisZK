import Aeneas
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result

/-! Reuses the checked R306 reverse-range source proofs; only the proof owner
namespace/imports are changed. No field or protocol relation is assumed. -/
namespace AspisR1S9ReverseRangeProgressV1
noncomputable section

abbrev ReverseRange := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)

theorem wrapping_sub_one_val (n : Usize) (hn : 1 ≤ n.val) :
    (Usize.wrapping_sub n 1#usize).val = n.val - 1 := by
  rw [Usize.wrapping_sub_val_eq]
  have hb : n.val < UScalar.size .Usize := by
    simpa only [UScalar.size] using n.hBounds
  have h1 : (1#usize).val = 1 := by simp
  rw [h1]
  have he : n.val + (UScalar.size .Usize - 1) =
      (n.val - 1) + UScalar.size .Usize := by omega
  rw [he, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by omega)

theorem reverse_next_done (iter : ReverseRange)
    (hstop : iter.iter.end.val ≤ iter.iter.start.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
        .ok (none, iter) := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, bind_tc_ok]
  have h : ¬ iter.iter.start.val < iter.iter.end.val := by omega
  simp [h]

theorem reverse_next_step (iter : ReverseRange)
    (hstep : iter.iter.start.val < iter.iter.end.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
        .ok (some (Usize.wrapping_sub iter.iter.end 1#usize),
          ⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩) := by
  have he : 1 ≤ iter.iter.end.val := by omega
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, core.cmp.impls.PartialOrdUsize.lt, bind_tc_ok]
  simp only [hstep, decide_true, ↓reduceIte,
    core.iter.range.UScalarStep.backward_checked]
  simp only [show (1#usize).val = 1 from by simp, he, ↓reduceDIte, bind_tc_ok]
  have hp : @UScalar.ofNatCore .Usize (iter.iter.end.val - 1) (by scalar_tac) =
      Usize.wrapping_sub iter.iter.end 1#usize := by
    apply UScalar.eq_of_val_eq
    simp only [UScalar.ofNatCore_val_eq, wrapping_sub_one_val _ he]
  rw [hp]


theorem reverse_next_some_progress (iter iterNext : ReverseRange) (d : Usize)
    (hnext : core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) iter =
        .ok (some d, iterNext)) :
    iter.iter.start.val < iter.iter.end.val ∧
      d = Usize.wrapping_sub iter.iter.end 1#usize ∧
      iterNext.iter.start = iter.iter.start ∧
      iterNext.iter.end.val + 1 = iter.iter.end.val := by
  have hlt : iter.iter.start.val < iter.iter.end.val := by
    by_contra h
    have hdone := reverse_next_done iter (by omega)
    rw [hnext] at hdone
    cases hdone
  have hstep := reverse_next_step iter hlt
  have heq := Result.ok.inj (hstep.symm.trans hnext)
  have hdEq : some (Usize.wrapping_sub iter.iter.end 1#usize) = some d :=
    congrArg Prod.fst heq
  have hiter :
      (⟨{iter.iter with «end» := Usize.wrapping_sub iter.iter.end 1#usize}⟩ : ReverseRange) =
        iterNext := congrArg Prod.snd heq
  have hd : d = Usize.wrapping_sub iter.iter.end 1#usize := by
    injection hdEq with h
    exact h.symm
  refine ⟨hlt, hd, ?_, ?_⟩
  · rw [← hiter]
  · rw [← hiter]
    change (Usize.wrapping_sub iter.iter.end 1#usize).val + 1 = iter.iter.end.val
    rw [wrapping_sub_one_val _ (by omega)]
    omega

#print axioms reverse_next_done
#print axioms reverse_next_step
#print axioms reverse_next_some_progress
end
end AspisR1S9ReverseRangeProgressV1
