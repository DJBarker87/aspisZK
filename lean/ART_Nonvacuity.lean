import ART_QueriedCoverage
import ART_NativeAccepted
import ART_AccountAccepted
import ART_FirstProjection
import ARS_WorldCylinder
import ARS_Coverage
import JFx_NativeBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

/-- Conditional SAME real-byte installed pair, never a fabricated accepted
wrapper. Waiting on the complete composition beyond JFm_Begin.source /
JFm_Q14Source.semantic and JFn_TX2.partial_on_saved /
JFn_Nonvacuity.inhabited: those are partial predecessors, not accepted2. -/
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
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (realBytes : (eval native (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission)) :
    Nonempty (ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) ∧
    (eval H (submission a)).2 =
      (⟨MultiproofConeCanonical.bytesOf JFx_NativeBytes.publicBytes,
        MultiproofConeCanonical.bytesOf JFx_NativeBytes.proofBytes⟩ : F3T_ByteCarrier.Submission) ∧
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account
      (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
  let cfg := FIp_Install.configuration err c r
  have original := ART_NativeAccepted.accepted L copy allocator c err r native1 native2 hashv extraction a native n
  have same := ARS_AccountReplay.replay _ native H consistent
  have yes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a)).2 = true := by
    rw [same]; exact original
  have totalSame : eval H (SCE_Experiment.account cfg hashv copy allocator CPH_Program.verifier a) =
      eval native (SCE_Experiment.account cfg hashv copy allocator CPH_Program.verifier a) :=
    (ART_AccountAccepted.exact cfg hashv copy allocator CPH_Program.verifier a H yes).symm.trans
      (same.trans (ART_AccountAccepted.exact cfg hashv copy allocator CPH_Program.verifier a native original))
  have totalConsistent := ARS_WorldCylinder.agrees_of_same native H _ totalSame
  have support := ARS_Coverage.deployed L copy allocator c err r native1 native2 hashv extraction a native H n totalConsistent
  refine ⟨support.1,?_,yes⟩
  have firstSame : (eval H a.first).2 = (eval native a.first).2 := by
    rw [←ART_FirstProjection.original cfg hashv copy allocator CPH_Program.verifier a H,
      ←ART_FirstProjection.original cfg hashv copy allocator CPH_Program.verifier a native,same]
  simpa only [submission_eval,firstSame] using realBytes

#print axioms conditional
end AspisR1.ART_Nonvacuity
end
