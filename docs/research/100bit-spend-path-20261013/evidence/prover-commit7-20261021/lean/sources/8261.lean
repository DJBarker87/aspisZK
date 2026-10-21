import R1Z.ProverCommitCallerNext

set_option autoImplicit false
namespace R1Z.ProverCommitCallerLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1ProverCaller7
open R1Z.ProverCommitCallerNext

theorem iterator_more (attempts : I32) (running : attempts.val < 16) :
    ∃ after : core.ops.range.Range I32,
      core.iter.range.IteratorRange.next core.iter.range.StepI32
        {start := attempts, «end» := 16#i32} = ok (some attempts, after) ∧
      after.start.val = attempts.val + 1 ∧ after.end = 16#i32 := by
  have hmax : attempts.val + 1 ≤ IScalar.max .I32 := by scalar_tac
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.PartialOrdI32,
    core.cmp.impls.PartialOrdI32.lt, core.clone.CloneI32,
    core.clone.impls.CloneI32.clone, liftFun1, liftFun2, bind_tc_ok]
  simp [running, core.iter.range.IScalarStep.forward_checked, hmax]

theorem iterator_done (attempts : I32) (stopped : 16 ≤ attempts.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32
      {start := attempts, «end» := 16#i32} =
      ok (none, {start := attempts, «end» := 16#i32}) := by
  simp [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.PartialOrdI32,
    core.cmp.impls.PartialOrdI32.lt, not_lt.mpr stopped]

#print axioms iterator_more
#print axioms iterator_done
end R1Z.ProverCommitCallerLoop
