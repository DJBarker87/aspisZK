import ARV_FilterOriginal
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterWeighted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
open scoped BigOperators

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem original_law {I : Type} [Fintype I]
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (native H : I → Bytes → State)
    (entries : ∀ i, ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a (native i))
    (syscall : ∀ i, S2W_ExtractionBoundary.RuntimeSyscall hashv (native i))
    (consistent : ∀ i, ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) (native i) (H i))
    (weight : I → Rat)
    (observe : (List (Bytes × State) × Option F3T_Experiment.RunView) → Rat) :
    (∑ i, weight i * observe (eval (H i) (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a))) =
      ∑ i, weight i * observe (eval (native i) (ART_Runtime.runtime (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier a)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [ARV_FilterOriginal.preserved L copy allocator c err r native1 native2 hashv a extraction
    (native i) (H i) (entries i) (syscall i) (consistent i)]

#print axioms original_law
end AspisR1.ARV_FilterWeighted
end
