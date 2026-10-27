import RPz7_GExq_WrapperCode
import RPz8_SCG_CodeMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_WrapperLog
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_WrapperLaws
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

local instance : MonadLift Result SdkC_Source.Code where
  monadLift := CheckpointBytes5Effect.liftResult

theorem lifted {B : Type} (r : Result B) :
    SdkC_Oracle.program (liftM r : SdkC_Source.Code B) = .done r := by
  cases r <;> rfl

theorem purely {B : Type} (b : B) :
    SdkC_Oracle.program (pure b : SdkC_Source.Code B) = .done (ok b) := rfl

/-- Allocation/copy/cleanup add no oracle reads around the caller body.
The reservation success is an intermediate fact, not a proposed top premise. -/
theorem first {A : Type} (body : SdkC_Source.Code S2W_Observation.Answer)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (e : Entry) (state allocated : A)
    (reserved : reserve allocator (admittedSizes e 3 firstSizes) state = ok allocated)
    (H : Bytes → State) :
    (eval H (SdkC_Oracle.program (GExq_WrapperCode.first body copy allocator e state))).1 =
      (eval H (SdkC_Oracle.program body)).1 := by
  unfold GExq_WrapperCode.first
  rw [DrvC_OraclePort.program_bindM,lifted]
  simp only [DrvC_OraclePort.bindR,eval_bind,reserved,VTop_OracleCode.continueWith,eval,List.nil_append]
  rw [DrvC_OraclePort.program_bindM]
  simp only [DrvC_OraclePort.bindR,eval_bind]
  cases hb : (eval H (SdkC_Oracle.program body)).2 with
  | fail error => simp only [hb,VTop_OracleCode.continueWith,eval,List.append_nil]
  | div => simp only [hb,VTop_OracleCode.continueWith,eval,List.append_nil]
  | ok result =>
    cases result with
    | Err error => simp only [hb,VTop_OracleCode.continueWith,purely,eval,List.append_nil]
    | Ok saved =>
      simp only [hb,VTop_OracleCode.continueWith]
      split
      · rw [DrvC_OraclePort.program_liftM]
        simp only [eval,List.append_nil]
      · rw [DrvC_OraclePort.program_bindM,lifted]
        simp only [DrvC_OraclePort.bindR,eval_bind,eval,List.append_nil]
        cases allocator.cleanup allocated <;> simp only [VTop_OracleCode.continueWith,purely,eval,List.append_nil]

/-- TX2 allocation and cleanup likewise preserve the body's complete log. -/
theorem second {A : Type} (body : SdkC_Source.Code (core.result.Result Unit AdapterRw.Cuts.PE))
    (allocator : Allocator A) (e : Entry) (state allocated : A)
    (reserved : reserve allocator (admittedSizes e 7 secondSizes) state = ok allocated)
    (H : Bytes → State) :
    (eval H (SdkC_Oracle.program (GExq_WrapperCode.second body allocator e state))).1 =
      (eval H (SdkC_Oracle.program body)).1 := by
  unfold GExq_WrapperCode.second
  rw [DrvC_OraclePort.program_bindM,lifted]
  simp only [DrvC_OraclePort.bindR,eval_bind,reserved,VTop_OracleCode.continueWith,eval,List.nil_append]
  rw [DrvC_OraclePort.program_bindM]
  simp only [DrvC_OraclePort.bindR,eval_bind]
  cases hb : (eval H (SdkC_Oracle.program body)).2 with
  | fail error => simp only [hb,VTop_OracleCode.continueWith,eval,List.append_nil]
  | div => simp only [hb,VTop_OracleCode.continueWith,eval,List.append_nil]
  | ok result =>
    cases result with
    | Err error => simp only [hb,VTop_OracleCode.continueWith,purely,eval,List.append_nil]
    | Ok unit =>
      cases unit
      simp only [hb,VTop_OracleCode.continueWith]
      rw [DrvC_OraclePort.program_bindM,lifted]
      simp only [DrvC_OraclePort.bindR,eval_bind,eval]
      cases allocator.cleanup allocated <;> simp only [VTop_OracleCode.continueWith,purely,eval,List.append_nil]

#print axioms purely
#print axioms lifted
#print axioms first
#print axioms second
end AspisR1.SCG_WrapperLog
end
