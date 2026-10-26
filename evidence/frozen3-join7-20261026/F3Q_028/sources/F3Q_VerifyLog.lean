import F3Q_CodeLog
import F3N_P6LevelLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_VerifyLog
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConePhysicalViews

theorem code_log (H : Bytes → State) (root : Array U8 32#usize) (s : reference.Scratch)
    (nodes : Slice U8) (nonzero : s.n≠0#usize) (bounded : ¬s.n>16#usize)
    (valid : reference.valid_indices s.idx s.n 0#usize=ok true)
    (multiple : Slice.len nodes % 32#usize=ok 0#usize) :
    (eval H (SdkC_Oracle.program (Port9OR_P6Verify.code root s nodes))).1=
      (eval H (SdkC_Oracle.program (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes))).1 := by
  unfold Port9OR_P6Verify.code
  simp only [if_neg nonzero,if_neg bounded,Bind.bind,F3Q_CodeEval.lift_bind_eval,valid,multiple]
  change (eval H (SdkC_Oracle.program (CheckpointBytes5Effect.bind
    (Port9OR_P6Levels.levels 18 {s with «at»:=0#usize} nodes)
    (fun out=>CheckpointBytes5Effect.liftResult (Port9OR_P6Verify.after root nodes out))))).1=_
  exact F3Q_CodeLog.lift_tail H _ _

#print axioms code_log
end AspisR1.F3Q_VerifyLog
end
