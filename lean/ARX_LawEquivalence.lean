import ARX_AdmittedRuntime
import ARW_AdmittedBudget
import ARW_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_LawEquivalence
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


variable (extraction : S2W_DigestExtraction.AeneasExtraction
    (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
include extraction

/-- Equality of arbitrary outcome/cost observations, not acceptance alone. -/
theorem observations (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    {V : Type} (observe : View Bytes State (Option F3T_Experiment.RunView) → V) :
    observe (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)) =
    observe (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)) := by
  rw [ARX_AdmittedRuntime.on_admitted L copy allocator c err r native1 native2 hashv a extraction H n]

/-- Full issued work including reached adaptive second choice, unchanged. -/
theorem work (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length =
      ART_AdversaryWork.work (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H :=
  ARW_AdmittedQueries.admitted L copy allocator c err r native1 native2 hashv extraction a H n

omit extraction

/-- Whole-ROM integral restricted by zero extension. No division by support mass. -/
def admittedMean (observe : F3T_Experiment.RunView → Rat) : Rat :=
  lazyMean (ART_PartialAccount.account (FIp_Install.configuration err c r)
    hashv copy allocator CPH_Program.verifier a) FS.emptyTable fun v =>
      if ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a v
      then observe (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input
        (FIp_Install.configuration err c r) (submitted v.2.1)),accepted v.2)) else 0

theorem mean (observe : F3T_Experiment.RunView → Rat) :
    lazyMean (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)
      FS.emptyTable (fun v => match v.2 with | none => 0 | some run => observe run) =
    admittedMean (Tx := Tx) L copy allocator c err r native1 native2 hashv a observe := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  simp only [ARX_AdmittedRuntime.runtime,eval_bind,OracleProgramRecording.eval_record,
    eval,List.append_nil]
  split_ifs <;> rfl

theorem failure_mean :
    F3T_Runtime.deployedFailure (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
    admittedMean (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (fun run => RawRecordedOracleExtractionMassBin.failureMass (F3T_Experiment.view run)) :=
  mean L copy allocator c err r native1 native2 hashv a _

#print axioms observations
#print axioms work
#print axioms mean
#print axioms failure_mean
end AspisR1.ARX_LawEquivalence
end
