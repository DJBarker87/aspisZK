import RPz8_SCH_SdkPure
import RPz8_SCG_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_FirstChild
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local irreducible] GExq_FirstCode.code

/-- Invert the actual outer error conversions around the ideal TX1 child. -/
theorem accepted {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (H : Bytes → State)
    (semantic : AdapterRw.LeadInputs.Public) (pub proof : Slice U8) (split : Usize)
    (saved : alloc.vec.Vec U8)
    (success : AdapterRw.first_decoded (SCH_IdealSdk.dictionary c hashv H)
      semantic pub proof split = ok (.Ok saved)) :
    (eval H (SdkC_Oracle.program (GExq_FirstCode.code
      (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std hashv
      (AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std)))
      (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split ()))).2 = ok (.Ok saved) := by
  unfold AdapterRw.first_decoded at success
  rw [SCH_SdkPure.digest] at success
  simp only [AdapterRw.observer,bind_tc_ok] at success
  dsimp only [SCH_IdealSdk.dictionary] at success
  dsimp only [GExq_ChildCode.execute] at success
  rw [DrvC_OraclePort.program_bindM] at success
  simp only [DrvC_OraclePort.bindR,eval_bind] at success
  cases hb : (eval H (SdkC_Oracle.program (GExq_FirstCode.code
      (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std hashv
      (AspisS6CurrentFirstInstallation.toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved c.query c.geometry c.boundaries c.std)))
      (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split ()))).2 with
  | fail e => simp only [hb,VTop_OracleCode.continueWith,eval,bind_tc_fail] at success; cases success
  | div => simp only [hb,VTop_OracleCode.continueWith,eval,bind_tc_div] at success; cases success
  | ok r =>
    cases r with
    | Err e =>
      simp only [hb,VTop_OracleCode.continueWith,SdkC_Oracle.program,eval,bind_tc_ok,
        SdkD_FirstChild.answer,AspisS6CurrentCodecInstallation.mapBoth,AdapterRw.core.result.Result.map_err] at success
      repeat' first
      | (solve | cases success)
      | uncase_result
      | head_reduce success
      | split at success
    | Ok result =>
      simp only [hb,VTop_OracleCode.continueWith,SdkC_Oracle.program,eval,bind_tc_ok,
        SdkD_FirstChild.answer,AspisS6CurrentCodecInstallation.mapBoth,AdapterRw.core.result.Result.map_err,id_eq] at success
      cases core.result.Result.Ok.inj (Result.ok.inj success)
      rfl

#print axioms accepted
end AspisR1.SCH_FirstChild
end
