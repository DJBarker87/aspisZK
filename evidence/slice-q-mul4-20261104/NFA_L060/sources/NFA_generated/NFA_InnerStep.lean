import NEV_DotEightTotal
import NEV_DotReadDomain
import Port3_PushFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFA_InnerStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1
/-- Successful actual native-model term steps preserve the SAME eight-word
bound. Scalar canonicality follows from its actual parser, with no byte premise. -/
theorem accepted (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (canonical : NEV_DotInputs.Canonical g) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize)
    (n : Nat) (active : n<4) (inside : iter.start.val<iter.end.val)
    (endpoint : iter.end.val≤26) (invariant : NEV_DotSweep.Sweep n 0 sums)
    (next : core.ops.range.Range Usize) (out : Array U64 8#usize)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=
      ok (cont (next,out))) :
    next.start.val=iter.start.val+1 ∧ next.end=iter.end ∧
      NEV_DotSweep.Sweep (n+1) 0 out := by
  obtain ⟨⟨o,cursor⟩,advance,value,start,finish⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter inside)
  subst o
  rw [NEV_ActualDotStep.body] at run
  simp only [NEV_ActualDotStep.step,advance,bind_tc_ok] at run
  obtain ⟨scalar,read,update⟩:=Port3_PushFrame.bind_success _ _ _ run
  have scalarCanonical:=NEV_DotReadDomain.reached q slot iter.start scalar read
  obtain ⟨result,actual,bound⟩:=NEV_DotEightTotal.suffix g canonical iter.start
    (by omega) scalar scalarCanonical n active sums invariant
  simp only [actual,bind_tc_ok] at update
  have same:=ControlFlow.cont.inj (Result.ok.inj update)
  have cursors : cursor=next:=congrArg Prod.fst same
  have outputs : result=out:=congrArg Prod.snd same
  exact ⟨by simpa only [cursors] using start,by simpa only [cursors] using finish,outputs ▸ bound⟩
/-- An active actual range iteration cannot terminate the loop early. -/
theorem shape (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (iter : core.ops.range.Range Usize)
    (sums : Array U64 8#usize) (inside : iter.start.val<iter.end.val)
    (flow : ControlFlow (core.ops.range.Range Usize × Array U64 8#usize) (Array U64 8#usize))
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot iter sums=ok flow) :
    ∃ next out,flow=cont (next,out) := by
  obtain ⟨⟨o,cursor⟩,advance,value,start,finish⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter inside)
  subst o
  rw [NEV_ActualDotStep.body] at run
  simp only [NEV_ActualDotStep.step,advance,bind_tc_ok] at run
  obtain ⟨scalar,read,update⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨out,update,tag⟩:=Port3_PushFrame.bind_success _ _ _ update
  exact ⟨cursor,out,(Result.ok.inj tag).symm⟩
#print axioms accepted
#print axioms shape
end NFA_InnerStep
end
