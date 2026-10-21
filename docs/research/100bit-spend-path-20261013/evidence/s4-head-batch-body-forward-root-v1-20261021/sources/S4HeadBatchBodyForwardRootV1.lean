import S4HeadBatchTermsForwardRootV1
import S4LimbLoopForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadBatchBodyForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cell cap)
open AspisR1FastDotsHeadBatchTermsForwardRootV1 (ParsedAt term_loop_forward)
open AspisR1FastDotsCurrentHeadTermForwardRootV1 (install)
open AspisR1FastDotsLimbFoldForwardRootV1 (limbCap)
abbrev StepBy := core.iter.adapters.step_by.StepBy Range
abbrev BatchBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body

theorem batch_body_forward
    (base : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot start : Usize) (iter iter' : StepBy) (limbs : Array Std.U64 8#usize) (b : Nat)
    (hn : core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter = .ok (some start,iter'))
    (hs : start.val<26) (hbudget : b+8≤64)
    (hcoords : ∀ j : Fin 29, AspisR1FastDotsWideLimbCanonical.CoordinateBound
      (g.val[j.val]'(by simpa [g.property] using j.isLt)))
    (hparsed : ∀ term : Usize, term.val<26 → ParsedAt a g slot term)
    (hinput : ∀ j : Fin 8, cell limbs j≤b*limbCap) :
    ∃ out : Array Std.U64 8#usize,
      BatchBody (install base) a g slot iter limbs = .ok (.cont (iter',out)) ∧
      (∀ j : Fin 8, cell out j≤(b+8)*limbCap) := by
  obtain ⟨endArg,ha,hav⟩ := AspisR1FastDotsFirstTailReadTotalRootV1.small_checked_add start 4#usize
    (by change start.val+4<1024; omega)
  change endArg.val=start.val+4 at hav
  let finish : Usize := if endArg<26#usize then endArg else 26#usize
  have hmin : core.cmp.min core.cmp.OrdUsize endArg 26#usize = .ok finish := by
    simp only [core.cmp.min,core.cmp.OrdUsize,core.cmp.impls.OrdUsize.min]
    rfl
  have hg : start.val≤finish.val ∧ finish.val≤26 ∧ finish.val-start.val≤4 := by
    by_cases hlt : endArg<26#usize
    · have hlt' : endArg.val<26 := hlt
      have he : finish=endArg := by simp only [finish,if_pos hlt]
      rw [he]
      omega
    · have hge : 26≤endArg.val := by change ¬ endArg.val<26 at hlt; omega
      have he : finish=26#usize := by simp only [finish,if_neg hlt]
      rw [he]
      change start.val≤26 ∧ 26≤26 ∧ 26-start.val≤4
      omega
  have hz : ∀ j : Fin 8, cell (Array.repeat 8#usize 0#u64) j≤0*cap := by
    intro j
    change ((List.replicate 8 (0#u64))[j.val]'(by simpa only [List.length_replicate] using j.isLt)).val≤0*cap
    rw [List.getElem_replicate]
    exact Nat.le_refl 0
  obtain ⟨sums,ht,hsums⟩ := term_loop_forward base a g slot start finish
    (Array.repeat 8#usize 0#u64) 0 hg.1 hg.2.1 (by omega) hcoords
    (by intro term _ he; exact hparsed term (by omega)) hz
  obtain ⟨out,hl,hout⟩ := AspisR1FastDotsLimbLoopForwardRootV1.limb_loop_forward
    (install base) sums limbs 0#usize b (by decide) (by simpa using hbudget) hinput
  have hout' : ∀ j : Fin 8, cell out j≤(b+8)*limbCap := by simpa using hout
  refine ⟨out,?_,hout'⟩
  have hc : (install base).wideLimbCount=.ok 8#usize := rfl
  simp only [BatchBody,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body,
    hn,hc,bind_tc_ok]
  change ((do
    let arg ← start+4#usize
    let finish1 ← core.cmp.min core.cmp.OrdUsize arg 26#usize
    let sums1 ← AspisR1FastDotsHeadBatchTermsForwardRootV1.TermLoop (install base)
      {start:=start,«end»:=finish1} a g slot (Array.repeat 8#usize 0#u64)
    let limbs1 ← AspisR1FastDotsLimbFoldForwardRootV1.LimbLoop (install base)
      {start:=0#usize,«end»:=8#usize} limbs sums1
    .ok (.cont (iter',limbs1))) : Result (ControlFlow
      (StepBy × Array Std.U64 8#usize) (Array Std.U64 8#usize))) = .ok (.cont (iter',out))
  simp only [ha,hmin,ht,hl,bind_tc_ok]

#print axioms batch_body_forward
end AspisR1FastDotsHeadBatchBodyForwardRootV1
