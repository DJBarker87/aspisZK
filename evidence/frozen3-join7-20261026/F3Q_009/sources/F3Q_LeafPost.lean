import F3Q_CodeEval
import Port9OR_BatchStep
import Port4B_LeafStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_LeafPost
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port9OR_BatchStep (Indices Values Next Out)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

def code (idx : Indices) (val : Values) (d : Usize) (index : U32)
    (leaf : Array U8 32#usize) (pos : Usize) : Code (ControlFlow Next Out) :=
  let ops := Port9OR_BatchStep.ops Port4B_Install.leaves
  do
      if d > 0#usize
      then
        let i4 ← liftResult (
          lift (Std.Usize.wrapping_sub d 1#usize)
          )
        let b ← liftResult (
          ops.op8 idx i4 index
          )
        if b
        then
          let i5 ← liftResult (
            lift (Std.Usize.wrapping_sub d 1#usize)
            )
          let b1 ← liftResult (
            ops.op7 val i5 leaf
            )
          if b1
          then pure (cont (idx, val, d, pos))
          else
            pure (done (idx, val, some (core.result.Result.Err
              verifier.Error.Merkle)))
        else
          let idx1 ← liftResult (
            Array.update idx d index
            )
          let val1 ← liftResult (
            Array.update val d leaf
            )
          let d1 ← liftResult (
            lift (Std.Usize.wrapping_add d 1#usize)
            )
          pure (cont (idx1, val1, d1, pos))
      else
        let idx1 ← liftResult (
          Array.update idx d index
          )
        let val1 ← liftResult (
          Array.update val d leaf
          )
        let d1 ← liftResult (
          lift (Std.Usize.wrapping_add d 1#usize)
          )
        pure (cont (idx1, val1, d1, pos))

theorem eval_post (H : Bytes → State) (idx : Indices) (val : Values) (d : Usize) (index : U32)
    (leaf : Array U8 32#usize) (pos : Usize) :
    eval H (SdkC_Oracle.program (code idx val d index leaf pos))=
      ([],Port4B_LeafStep.post idx val d index leaf pos) := by
  unfold code Port4B_LeafStep.post
  simp only [F3Q_CodeEval.bind_eval,F3Q_CodeEval.lift_bind_eval,
    Port9OR_BatchStep.ops,Port3_BatchStd.install]
  repeat' first
  | (solve | rfl)
  | (split <;> simp_all only [if_true,if_false])
  | uncase_result
  all_goals rfl

#print axioms eval_post
end AspisR1.F3Q_LeafPost
end
