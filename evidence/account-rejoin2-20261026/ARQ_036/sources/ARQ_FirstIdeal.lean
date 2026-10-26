import ARQ_Installation
import F3V_FirstCode
import F3U_ReifyValue
import SCG_FirstCode
import SCH_IdealSdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_FirstIdeal
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A source-level mapped successful reply retains its original saved Vec. -/
theorem answer_ok (r : core.result.Result (alloc.vec.Vec U8) AspisR1CurrentCaller.verifier.Error)
    (saved : alloc.vec.Vec U8) (same : SdkD_FirstChild.answer r = .Ok saved) : r = .Ok saved := by
  cases r with
  | Err error => cases same
  | Ok v => exact congrArg core.result.Result.Ok (core.result.Result.Ok.inj same)

/-- Ideal op10 success is success of its actual GExp code, on the same operands.
It is not an ideal-to-native reversal through RuntimeSyscall. -/
theorem code {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (called : (SCH_IdealSdk.dictionary c hashv H).op10
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (SCH_IdealSdk.dictionary c hashv H))
        semantic pub proof split () none = ok (.Ok saved)) :
    (eval H (SdkC_Oracle.program
      (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std hashv
        (AspisS6CurrentFirstInstallation.toDigest
          (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
            (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
              c.query c.geometry c.boundaries c.std)))
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split))).2 = ok (.Ok saved) := by
  change (eval H (SdkC_Oracle.program
    (CheckpointBytes5Effect.bind
      (GExq_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std hashv
        (AspisS6CurrentFirstInstallation.toDigest
          (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
            (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
              c.query c.geometry c.boundaries c.std)))
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split ())
      (fun r => .done (SdkD_FirstChild.answer r))))).2 = _ at called
  rw [SCG_FirstCode.code,DrvC_OraclePort.program_bindM] at called
  simp only [DrvC_OraclePort.bindR,eval_bind] at called
  cases h : (eval H (SdkC_Oracle.program
    (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std hashv
      (AspisS6CurrentFirstInstallation.toDigest
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
            c.query c.geometry c.boundaries c.std)))
      (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split))).2 with
  | fail e => simp only [h,VTop_OracleCode.continueWith,eval] at called; cases called
  | div => simp only [h,VTop_OracleCode.continueWith,eval] at called; cases called
  | ok r =>
    simp only [h,VTop_OracleCode.continueWith,eval] at called
    exact congrArg Result.ok (answer_ok r saved (Result.ok.inj called))

#print axioms answer_ok
#print axioms code
end AspisR1.ARQ_FirstIdeal
end
