import ARU_Coverage
import ARU_PartialAccepted
import ARU_R1
import JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
/-- Conditional on the real accepted extracted pair still awaited beyond
JFm_Begin.source, JFm_Q14Source.semantic, JFn_TX2.partial_on_saved and
JFn_Nonvacuity.inhabited. None of those partial predecessors is accepted2. -/
theorem conditional {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (std : S2W_TrustedStd.TrustedStd copy)
    (consistent : ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (realBytes : (eval native (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission)) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    (eval H (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = true := by
  obtain ⟨m⟩ := ARU_Factory.deployed L copy allocator c err r native1 native2 hashv extraction a native H n consistent
  refine ⟨⟨m⟩,?_,(ARU_PartialAccepted.accepted L copy allocator c err r native1 native2 hashv extraction a H m).1⟩
  have first := ARS_AccountReplay.first (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a native H consistent
  simpa only [submission_eval,first] using realBytes

#print axioms conditional
end AspisR1.ARU_Nonvacuity
end
