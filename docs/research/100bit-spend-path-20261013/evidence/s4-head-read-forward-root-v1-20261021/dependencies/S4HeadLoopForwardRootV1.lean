import S4HeadLimbForwardRootV1
import S4TailRangeNextRootV1
import S4FirstTailReadTotalRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsHeadLoopForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (InnerLoop InnerBody Range cap cell)

theorem inner_loop_forward
    (ops : Ops) (k : Nat) (hk : k ≤ 3)
    (coefficient : Array Std.U32 8#usize) (start : Usize)
    (sums : Array Std.U64 8#usize) (scalar : M31)
    (hstart : start.val ≤ 8)
    (hcoeff : ∀ j : Fin 8,
      (coefficient.val[j.val]'(by simpa [coefficient.property] using j.isLt)).val < 2147483647)
    (hbase : ∀ j : Fin 8, cell sums j ≤ (k+1)*cap)
    (hsuffix : ∀ j : Fin 8, start.val ≤ j.val → cell sums j ≤ k*cap)
    (hscalar : scalar.val < 2147483647) :
    ∃ out : Array Std.U64 8#usize,
      InnerLoop ops {start:=start,«end»:=8#usize} sums scalar coefficient = .ok out ∧
      (∀ j : Fin 8, cell out j ≤ (k+1)*cap) := by
  induction hm : 8-start.val using Nat.strong_induction_on generalizing start sums with
  | h m ih =>
    by_cases he : start.val=8
    · have heq : start=8#usize := UScalar.eq_of_val_eq (by simpa using he)
      subst start
      obtain ⟨it,hn⟩ := AspisR1FastDotsTailRangeNextRootV1.range_next_done 8#usize
      have hb : InnerBody ops coefficient {start:=8#usize,«end»:=8#usize} sums scalar =
          .ok (.done sums) := by
        simp [InnerBody,
          AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body,hn]
      refine ⟨sums,?_,hbase⟩
      change loop (fun s : Range × Array Std.U64 8#usize × M31 =>
        InnerBody ops coefficient s.1 s.2.1 s.2.2)
        ({start:=8#usize,«end»:=8#usize},sums,scalar) = .ok sums
      rw [loop.eq_def]
      simpa only [hb,bind_tc_ok]
    · have hi : start.val<8 := by omega
      obtain ⟨next,_ha,hval⟩ := AspisR1FastDotsFirstTailReadTotalRootV1.small_checked_add start 1#usize (by simpa using (show start.val+1<1024 by omega))
      have hv : next.val=start.val+1 := by simpa using hval
      have hn := AspisR1FastDotsTailRangeNextRootV1.range_next_succ start 8#usize next (by simpa using hi) hv
      obtain ⟨updated,hb,_,_,hs',hb'⟩ := inner_body_forward_linear_step ops k hk coefficient
        {start:=start,«end»:=8#usize} {start:=next,«end»:=8#usize} sums scalar hi hn hcoeff hbase hsuffix hscalar
      obtain ⟨out,hl,ho⟩ := ih (8-next.val) (by omega) next updated (by omega) hb' hs' rfl
      refine ⟨out,?_,ho⟩
      change loop (fun s : Range × Array Std.U64 8#usize × M31 =>
        InnerBody ops coefficient s.1 s.2.1 s.2.2)
        ({start:=next,«end»:=8#usize},updated,scalar) = .ok out at hl
      change loop (fun s : Range × Array Std.U64 8#usize × M31 =>
        InnerBody ops coefficient s.1 s.2.1 s.2.2)
        ({start:=start,«end»:=8#usize},sums,scalar) = .ok out
      rw [loop.eq_def]
      simpa only [hb,bind_tc_ok] using hl

#print axioms inner_loop_forward
end AspisR1FastDotsHeadLoopForwardRootV1
