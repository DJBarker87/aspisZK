import SCH_Lower
import S2W_TraceFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_LowerTrace
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_OuterLower

/-- Flatten the actual ideal child executions in returned-call order. -/
def trace {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (log : S2W_Trace.Log) : List (Bytes × State) :=
  log.flatMap fun ev => match ev with
    | .returned op _ => (eval H (SdkC_Oracle.program
      (GExq_Caller.child c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std hashv op))).1

/-- Oracle-world analogue of SCG_OuterLog.flatten. This does not invert
native syscall success: the dictionary is defined by the very ideal replies. -/
theorem flatten {F C A : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (code : Native A) (before after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H) code before = ok (value,after)) :
    trace c hashv H before ++
      (eval H (SdkC_Oracle.program (lower
        (GExq_Caller.child c.adapter c.currentBase c.stageBase c.finish c.reserved
          c.query c.geometry c.boundaries c.std hashv) code))).1 = trace c hashv H after := by
  induction code generalizing before after with
  | done a =>
    cases Result.ok.inj ran
    exact List.append_nil _
  | step r k ih =>
    cases r with
    | fail e => cases ran
    | div => cases ran
    | ok a => exact ih a before after ran
  | call op k ih =>
    rw [S2W_Trace.run,SCH_IdealSdkInvoke.invoke] at ran
    simp only [lower,DrvC_CallCode.program_bind,eval_bind]
    cases actual : (eval H (SdkC_Oracle.program
      (GExq_Caller.child c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std hashv op))).2 with
    | fail e => simp only [actual,S2W_Trace.thenResult] at ran; cases ran
    | div => simp only [actual,S2W_Trace.thenResult] at ran; cases ran
    | ok a =>
      simp only [actual,S2W_Trace.thenResult] at ran
      have next := ih a (before ++ [.returned op a]) after ran
      simp only [actual,VTop_OracleCode.continueWith]
      simpa only [trace,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,List.append_assoc] using next

#print axioms flatten
end AspisR1.ARQ_LowerTrace
end
