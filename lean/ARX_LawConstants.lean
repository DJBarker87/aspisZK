import ARX_LocalCharge
import ARW_AdmittedBudget
import F3T_Accounting
import F3T_Charged
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_LawConstants
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)


theorem unchanged
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (D : LiteralByteProtocol.Decoder) (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
    (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    let cfg := FIp_Install.configuration err c r
    let P := F3T_ByteCarrier.lift cfg (ARW_Induced.program native1 copy allocator CPH_Program.verifier a)
    DecodedFirstReadUnionBound.decoderFirstReads RecordedBinaryExperimentBin.dec FS.emptyTable
      (eval H (F3T_Charged.charged D (F3T_Canon.canon P))).1 ≤ Q0+Q1+34 ∧
    FS.firstReads FS.emptyTable (eval H (F3T_Charged.projected D (F3T_Canon.canon P))).1 ≤ Q0+Q1+1161 ∧
    (eval H (F3T_Charged.projected D (F3T_Canon.canon P))).1.length ≤ Q0+Q1+2322 ∧
    FS.firstReads FS.emptyTable (eval H (Hiq_RecordedJoint.program
      (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)
      ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier))).1 ≤ Q0+Q1+2965 := by
  dsimp only
  let cfg := FIp_Install.configuration err c r
  let P := F3T_ByteCarrier.lift cfg (ARW_Induced.program native1 copy allocator CPH_Program.verifier a)
  have q : ∀ K, (eval K P).1.length ≤ Q0+Q1 := by
    intro K
    rw [F3T_ByteCarrier.lift_eval,ARW_Induced.queries]
    exact queries K
  refine ⟨F3T_Charged.starts D (F3T_Canon.canon P) (Q0+Q1) (F3T_Canon.bound P _ q) H,
    F3T_Accounting.first_reads D P _ q H,F3T_Accounting.log_length D P _ q H,?_⟩
  let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
  have budget := (ARW_AdmittedBudget.issued L copy allocator c err r native1 native2 hashv extraction a H n Q0 Q1 queries).2
  have same := ARX_LocalCharge.exact source (Q0+Q1) H budget
  have full := F3T_AccountCharge.reads (ARX_LocalCharge.bounded source (Q0+Q1)) ARQ_Observer.project
    (ARQ_Observer.select cfg CPH_Program.verifier) (Q0+Q1)
    (fun K => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget source (Q0+Q1) K)) H
  rw [ARX_LocalCharge.congr_source _ _ ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier) H same] at full
  exact full
#print axioms unchanged
end AspisR1.ARX_LawConstants
end
