import RPz8_SCG_WrapperLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_WrapperFirst
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Ideal wrapper success inverts to the same saved value at its body,
without reversing the native-to-ideal syscall theorem. -/
theorem body {A : Type} (code : SdkC_Source.Code S2W_Observation.Answer)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (H : Bytes → State)
    (success : (eval H (SdkC_Oracle.program
      (GExq_WrapperCode.first code copy allocator e state))).2 = ok (.Ok (saved,post,final))) :
    ∃ allocated, reserve allocator (admittedSizes e 3 firstSizes) state = ok allocated ∧
      (eval H (SdkC_Oracle.program code)).2 = ok (.Ok saved) := by
  unfold GExq_WrapperCode.first at success
  rw [DrvC_OraclePort.program_bindM,SCG_WrapperLog.lifted] at success
  simp only [DrvC_OraclePort.bindR,AspisV8R19.OracleProgramOps.eval_bind] at success
  cases hr : reserve allocator (admittedSizes e 3 firstSizes) state with
  | fail err => simp only [hr,VTop_OracleCode.continueWith,eval] at success; cases success
  | div => simp only [hr,VTop_OracleCode.continueWith,eval] at success; cases success
  | ok allocated =>
    simp only [hr,VTop_OracleCode.continueWith,eval] at success
    rw [DrvC_OraclePort.program_bindM] at success
    simp only [DrvC_OraclePort.bindR,AspisV8R19.OracleProgramOps.eval_bind] at success
    cases hb : (eval H (SdkC_Oracle.program code)).2 with
    | fail err => simp only [hb,VTop_OracleCode.continueWith,eval] at success; cases success
    | div => simp only [hb,VTop_OracleCode.continueWith,eval] at success; cases success
    | ok result =>
      cases result with
      | Err err => simp only [hb,VTop_OracleCode.continueWith,SCG_WrapperLog.purely,eval] at success; cases success
      | Ok returned =>
        simp only [hb,VTop_OracleCode.continueWith] at success
        split at success
        · rw [DrvC_OraclePort.program_liftM] at success
          cases success
        · rw [DrvC_OraclePort.program_bindM,SCG_WrapperLog.lifted] at success
          simp only [DrvC_OraclePort.bindR,AspisV8R19.OracleProgramOps.eval_bind,eval] at success
          cases hc : allocator.cleanup allocated with
          | fail err => simp only [hc,VTop_OracleCode.continueWith,eval] at success; cases success
          | div => simp only [hc,VTop_OracleCode.continueWith,eval] at success; cases success
          | ok cleaned =>
            simp only [hc,VTop_OracleCode.continueWith,SCG_WrapperLog.purely,eval] at success
            have equal := core.result.Result.Ok.inj (Result.ok.inj success)
            have same : returned = saved := congrArg Prod.fst equal
            subst returned
            exact ⟨allocated,rfl,rfl⟩

#print axioms body
end AspisR1.SCH_WrapperFirst
end
