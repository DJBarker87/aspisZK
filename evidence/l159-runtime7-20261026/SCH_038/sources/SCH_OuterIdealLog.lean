import SCH_Lower
import SCH_TraceExists
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_OuterIdealLog
open Aeneas Aeneas.Std Result GExq_OuterLower
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)

abbrev child {A : Type} (call : S2W_Trace.Call A) := GExq_Caller.child c.adapter c.currentBase c.stageBase c.finish
  c.reserved c.query c.geometry c.boundaries c.std hashv call

def event : S2W_Trace.Event → List (Bytes × State)
  | .returned call _ => (eval H (SdkC_Oracle.program (child c hashv call))).1

def trace (log : S2W_Trace.Log) := log.flatMap (event c hashv H)

/-- Exact ideal ordered reads, including duplicate child queries. Every event
and return is reified from this world's interpreter, not imported from a
successful native run in another world. -/
theorem flatten {A : Type} (code : Native A) (before after : S2W_Trace.Log) (value : A)
    (ran : S2W_Trace.run (SCH_IdealSdk.dictionary c hashv H) code before = ok (value,after)) :
    trace c hashv H before ++
      (eval H (SdkC_Oracle.program (lower (child c hashv) code))).1 =
      trace c hashv H after := by
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
    cases actual : S2W_Trace.invoke (SCH_IdealSdk.dictionary c hashv H) op with
    | fail e => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | div => simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran; cases ran
    | ok a =>
      have called : (eval H (SdkC_Oracle.program (child c hashv op))).2 = ok a :=
        (SCH_IdealSdkInvoke.invoke c hashv H op).symm.trans actual
      simp only [S2W_Trace.run,actual,S2W_Trace.thenResult] at ran
      have next := ih a (before ++ [.returned op a]) after ran
      simp only [lower,DrvC_CallCode.program_bind,eval_bind,called,VTop_OracleCode.continueWith]
      simpa only [trace,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,event,
        List.append_nil,List.append_assoc] using next

#print axioms flatten
end AspisR1.SCH_OuterIdealLog
end
