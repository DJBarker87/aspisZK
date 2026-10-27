import ARX_AdmittedRuntime
import ARW_QueryAgreement
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_RejectedPrefixes
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

/-- Filtering outcome support never deletes any issued query prefix. -/
theorem cost (H : Bytes → State) :
    (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).1 =
    (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).1 := by
  rw [ARX_AdmittedRuntime.evaluation L copy allocator c err r native1 native2 hashv a extraction H,
    ART_Runtime.eval_runtime]

/-- A source rejection contributes exactly zero under either observer. -/
theorem mass (H : Bytes → State)
    (reject : accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = false) :
    F3T_Runtime.runtimeMass (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)) =
    F3T_Runtime.runtimeMass (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)) := by
  by_cases supported : Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
  · obtain ⟨n⟩ := supported
    rw [ARX_AdmittedRuntime.on_admitted L copy allocator c err r native1 native2 hashv a extraction H n]
  · have no := ARX_AdmittedRuntime.outside L copy allocator c err r native1 native2 hashv a extraction H supported
    rw [ART_Runtime.rejected _ hashv copy allocator CPH_Program.verifier a H reject]
    unfold F3T_Runtime.runtimeMass
    rw [no]

#print axioms cost
#print axioms mass
end AspisR1.ARX_RejectedPrefixes
end
