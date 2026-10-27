import RPz8_SCH_IdealSdkInvoke
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_Lower
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_OuterLower

/-- Every ideal caller result equals execution with its actual per-world
child interpreter. No accepted native observation or total syscall is used. -/
theorem result {F C A : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (code : Native A) :
    (eval H (SdkC_Oracle.program (lower
      (GExq_Caller.child c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std hashv) code))).2 =
      S2W_Trace.erase (SCH_IdealSdk.dictionary c hashv H) code := by
  induction code with
  | done a => rfl
  | step r k ih => cases r with
    | fail e => rfl
    | div => rfl
    | ok a => exact ih a
  | call op k ih =>
    simp only [lower,DrvC_CallCode.program_bind,
      AspisV8R19.OracleProgramOps.eval_bind,S2W_Trace.erase,SCH_IdealSdkInvoke.invoke]
    cases h : (eval H (SdkC_Oracle.program
      (GExq_Caller.child c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std hashv op))).2 with
    | fail e => simp only [h,VTop_OracleCode.continueWith,eval,bind_tc_fail]
    | div => simp only [h,VTop_OracleCode.continueWith,eval,bind_tc_div]
    | ok a => simpa only [h,VTop_OracleCode.continueWith,bind_tc_ok] using ih a

#print axioms result
end AspisR1.SCH_Lower
end
