import ARU_OriginalDomination
import ARU_Domination
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_OriginalAverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open AspisV8R19.CausalFirstHitUnionBound

open scoped BigOperators

/-- Original weights are unchanged. This finite-family theorem does NOT
identify arbitrary weights with the ROM lazyMean, and does not close the root. -/
theorem averaged {I W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : I → Bytes → State)
    (n : ∀ i, ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a (native i))
    (syscall : ∀ i, S2W_ExtractionBoundary.RuntimeSyscall hashv (native i))
    (consistent : ∀ i, ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) (native i) (H i))
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q : Nat) (bound : ART_AdversaryWork.Bound (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a Q)
    (worlds : Finset I) (weight : I → Rat) (nonnegative : ∀ i ∈ worlds, 0 ≤ weight i) :
    (∑ i ∈ worlds, weight i * RawRecordedOracleExtractionMassBin.failureMass (ART_PhysicalView.physical (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a (H i))) ≤
      (∑ i ∈ worlds, weight i * RawRecordedOracleExtractionMassBin.failureMass (eval (H i) (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a)))))) +
      (∑ i ∈ worlds, weight i * indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval (H i) (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))))) := by
  have each := fun i => ARU_OriginalDomination.pointwise L copy allocator c err r native1 native2 hashv extraction a
    (native i) (H i) (n i) (syscall i) (consistent i) std D words owners Q bound
  calc
    _ ≤ ∑ i ∈ worlds, weight i * (RawRecordedOracleExtractionMassBin.failureMass (eval (H i) (F3T_Charged.projected D (F3T_Canon.canon (F3T_ByteCarrier.lift (FIp_Install.configuration err c r) (submission a))))) + indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval (H i) (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))))) := by
      apply Finset.sum_le_sum
      intro i member
      exact mul_le_mul_of_nonneg_left (each i) (nonnegative i member)
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib]

#print axioms averaged
end AspisR1.ARU_OriginalAverage
end
