import RPz8_SCG_WrapperLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_WrapperSecond
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Second wrapper success selects the successful body on the same input. -/
theorem body {A : Type} (code : SdkC_Source.Code (core.result.Result Unit AdapterRw.Cuts.PE))
    (allocator : Allocator A) (e : Entry) (state final : A)
    (post : Heap (Nat → Record)) (H : Bytes → State)
    (success : (eval H (SdkC_Oracle.program
      (GExq_WrapperCode.second code allocator e state))).2 = ok (.Ok (post,final))) :
    ∃ allocated, reserve allocator (admittedSizes e 7 secondSizes) state = ok allocated ∧
      (eval H (SdkC_Oracle.program code)).2 = ok (.Ok ()) := by
  unfold GExq_WrapperCode.second at success
  rw [DrvC_OraclePort.program_bindM,SCG_WrapperLog.lifted] at success
  simp only [DrvC_OraclePort.bindR,AspisV8R19.OracleProgramOps.eval_bind] at success
  cases hr : reserve allocator (admittedSizes e 7 secondSizes) state with
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
      | Ok unit => cases unit; exact ⟨allocated,rfl,rfl⟩

#print axioms body
end AspisR1.SCH_WrapperSecond
end
