import ARS_Coverage
import JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_D189Consolidation

/-- Conditional only: the SAME extracted native pair must still be supplied.
JFp_SeededFixture.inhabited and JFo_Tail.source/native are partial predecessors,
not a jointly accepted pair theorem. No complete JFp/JFo theorem is presumed. -/
theorem conditional {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (consistent : ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (realBytes : (eval native (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission)) :
    Nonempty (ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    (eval H (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    SCE_Experiment.accepted (eval H
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
  obtain ⟨entry,_,accepted⟩ := ARS_Coverage.deployed L copy allocator c err r native1 native2 hashv
    extraction a native H n consistent
  refine ⟨entry,?_,accepted⟩
  rw [submission_eval,ARS_AccountReplay.first _ hashv copy allocator CPH_Program.verifier a native H consistent]
  simpa only [submission_eval] using realBytes

#print axioms conditional
end AspisR1.ARS_Nonvacuity
end
