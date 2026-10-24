import Port1_Driver
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port7CLEAN_Driver
open Aeneas Aeneas.Std Result VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Accepted driver stages expose the actual saved checkpoint and both
successes, with exact chronological logs. No independent TX2 run is chosen. -/
theorem accepted_stages (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (semantic : Port1_Driver.Semantic)
    (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (Port1_Driver.stages impl D hash semantic pub proof)).2=true) :
    ∃ saved : alloc.vec.Vec U8,
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved) ∧
      (eval H (interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).2=ok (.Ok ()) ∧
      (eval H (Port1_Driver.stages impl D hash semantic pub proof)).1=
        (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).1 ++
        (eval H (interpret impl (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).1 := by
  unfold Port1_Driver.stages at accepted ⊢
  simp only [eval_bind] at accepted ⊢
  cases first : (eval H (interpret impl
    (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2 with
  | fail e => simp only [first,eval,Bool.false_eq_true] at accepted
  | div => simp only [first,eval,Bool.false_eq_true] at accepted
  | ok result =>
    cases result with
    | Err e => simp only [first,eval,Bool.false_eq_true] at accepted
    | Ok saved =>
      simp only [first,eval_bind,eval,List.append_nil] at accepted ⊢
      cases second : (eval H (interpret impl
        (VTop_Flow.tx2_authenticated VTop_Flow.traceEffects D pub proof saved.deref hash none))).2 with
      | fail e => simp only [second,Port1_Driver.verdict,Bool.false_eq_true] at accepted
      | div => simp only [second,Port1_Driver.verdict,Bool.false_eq_true] at accepted
      | ok result =>
        cases result with
        | Err e => simp only [second,Port1_Driver.verdict,Bool.false_eq_true] at accepted
        | Ok unit => cases unit; exact ⟨saved,first,second,rfl⟩

#print axioms accepted_stages
end AspisR1.Port7CLEAN_Driver
end
