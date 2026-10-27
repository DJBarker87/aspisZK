import ARX_AdmittedRuntime
import ARX_LocalCharge
import ARX_LogAgreement
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_CappedSupport
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


theorem supported
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (Q : Nat) (H : Bytes → State)
    (yes : ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (eval H (ARX_LocalCharge.bounded (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a) Q))) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  obtain ⟨K,⟨n⟩,same⟩ := yes
  apply ARU_PartialFactory.original L copy allocator c err r native1 native2 hashv extraction a K H n
  exact ARX_LogAgreement.consistent _ K H _ (congrArg Prod.fst same)
    (Op5I_AcceptedCarrierCounterexample.evaluated_reply H _)
#print axioms supported
end AspisR1.ARX_CappedSupport
end
