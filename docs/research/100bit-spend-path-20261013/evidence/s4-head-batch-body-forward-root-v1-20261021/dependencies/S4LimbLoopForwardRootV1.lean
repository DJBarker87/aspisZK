import S4LimbFoldForwardRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsLimbLoopForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cell)
open AspisR1FastDotsLimbFoldForwardRootV1 (LimbBody LimbLoop limbCap limb_body_forward)

/-- A coarse execution envelope constructs every actual checked step.
Tighter retained per-coordinate bounds can be applied to the same successful
execution separately. No arithmetic or loop success is assumed. -/
theorem limb_loop_forward
    (ops : Ops) (sums limbs : Array Std.U64 8#usize) (start : Usize) (b : Nat)
    (hs : start.val≤8) (hbudget : b+(8-start.val)≤64)
    (hinput : ∀ j : Fin 8, cell limbs j≤b*limbCap) :
    ∃ out : Array Std.U64 8#usize,
      LimbLoop ops {start:=start,«end»:=8#usize} limbs sums = .ok out ∧
      (∀ j : Fin 8, cell out j≤(b+(8-start.val))*limbCap) := by
  induction hm : 8-start.val using Nat.strong_induction_on generalizing start limbs b with
  | h m ih =>
    by_cases he : start.val=8
    · have heq : start=8#usize := UScalar.eq_of_val_eq (by simpa using he)
      subst start
      obtain ⟨it,hn⟩ := AspisR1FastDotsTailRangeNextRootV1.range_next_done 8#usize
      have hb : LimbBody ops sums {start:=8#usize,«end»:=8#usize} limbs = .ok (.done limbs) := by
        simp [LimbBody,
          AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop1.body,hn]
      refine ⟨limbs,?_,?_⟩
      · change loop (fun st : Range × Array Std.U64 8#usize =>
          LimbBody ops sums st.1 st.2) ({start:=8#usize,«end»:=8#usize},limbs) = .ok limbs
        rw [loop.eq_def]
        simpa only [hb,bind_tc_ok]
      · have hm0 : m=0 := by change 8-8=m at hm; omega
        rw [hm0,Nat.add_zero]
        exact hinput
    · have hi : start.val<8 := by omega
      obtain ⟨next,_ha,hv⟩ := AspisR1FastDotsFirstTailReadTotalRootV1.small_checked_add start 1#usize
        (by change start.val+1<1024; omega)
      have hv' : next.val=start.val+1 := by simpa using hv
      have hn := AspisR1FastDotsTailRangeNextRootV1.range_next_succ start 8#usize next
        (by simpa using hi) hv'
      obtain ⟨updated,hb,hbnd⟩ := limb_body_forward ops sums limbs
        {start:=start,«end»:=8#usize} {start:=next,«end»:=8#usize} start b (by omega) hi hn hinput
      obtain ⟨out,hl,ho⟩ := ih (8-next.val) (by omega) updated next (b+1) (by omega) (by omega) hbnd rfl
      refine ⟨out,?_,?_⟩
      · change loop (fun st : Range × Array Std.U64 8#usize =>
          LimbBody ops sums st.1 st.2) ({start:=next,«end»:=8#usize},updated) = .ok out at hl
        change loop (fun st : Range × Array Std.U64 8#usize =>
          LimbBody ops sums st.1 st.2) ({start:=start,«end»:=8#usize},limbs) = .ok out
        rw [loop.eq_def]
        simpa only [hb,bind_tc_ok] using hl
      · have heq : b+m=(b+1)+(8-next.val) := by omega
        rw [heq]
        exact ho

#print axioms limb_loop_forward
end AspisR1FastDotsLimbLoopForwardRootV1
