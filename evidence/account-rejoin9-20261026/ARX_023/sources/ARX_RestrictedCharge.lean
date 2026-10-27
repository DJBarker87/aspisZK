import ARX_CappedSupport
import ARW_AdmittedBudget
import F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_RestrictedCharge
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


open AspisV8R19.CausalFirstHitUnionBound

/-- The full adaptive account charge, restricted without renormalization.
The original event and complete chronological source view are retained. -/
def chargeOn (source : Program Bytes State (GExq_AccountExperiment.Outcome A)) (Q : Nat) : Rat :=
  lazyMean (Hiq_RecordedJoint.program source ARQ_Observer.project
    (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier)) FS.emptyTable fun v =>
      if ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a v.2
      then indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) v) else 0

theorem equality
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1) :
    chargeOn (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) (Q0+Q1) =
    chargeOn (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (ARX_LocalCharge.bounded (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a) (Q0+Q1)) (Q0+Q1) := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  let source := ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a
  by_cases supported : Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
  · obtain ⟨n⟩ := supported
    have budget := (ARW_AdmittedBudget.issued L copy allocator c err r native1 native2 hashv extraction a H n Q0 Q1 queries).2
    have same := ARX_LocalCharge.exact source (Q0+Q1) H budget
    rw [ARX_LocalCharge.congr_source _ _ ARQ_Observer.project
      (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier) H same]
  · have noO : ¬ ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a (eval H source) :=
      fun yes => supported ((ARX_AdmittedRuntime.permitted_iff L copy allocator c err r native1 native2 hashv a extraction H).mp yes)
    have noC : ¬ ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a
        (eval H (ARX_LocalCharge.bounded source (Q0+Q1))) :=
      fun yes => supported (ARX_CappedSupport.supported L copy allocator c err r native1 native2 hashv a extraction (Q0+Q1) H yes)
    simp only [Hiq_RecordedJoint.source_view,if_neg noO,if_neg noC]

theorem bounded
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (Q0 Q1 : Nat)
    (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1) :
    chargeOn (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) (Q0+Q1) ≤
    F3T_Numeric.accountLoss (Q0+Q1) := by
  rw [equality L copy allocator c err r native1 native2 hashv a extraction Q0 Q1 queries]
  let source := ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a
  let capped := ARX_LocalCharge.bounded source (Q0+Q1)
  apply le_trans (b := F3T_AccountCharge.mass capped ARQ_Observer.project
    (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier) (Q0+Q1))
  · apply AllAddressFiatShamir.lazyMean_mono_of_eval
    intro H
    split_ifs <;> unfold indicator <;> split_ifs <;> norm_num
  · exact F3T_AccountCharge.bound capped ARQ_Observer.project
      (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier) (Q0+Q1)
      (fun H => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget source (Q0+Q1) H))

#print axioms equality
#print axioms bounded
end AspisR1.ARX_RestrictedCharge
end
