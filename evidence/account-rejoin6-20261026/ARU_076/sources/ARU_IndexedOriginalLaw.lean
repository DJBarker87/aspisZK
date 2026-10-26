import ARU_OriginalLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_IndexedOriginalLaw
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open scoped BigOperators

theorem original_law {I W A C Tx : Type} (L : Library W (Nat → Record))
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
    (worlds : Finset I) (weight : I → Rat)
    (observe : GExq_AccountExperiment.Outcome A → Nat → Rat) :
    (∀ i, Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a (H i))) ∧
    (∑ i ∈ worlds, weight i * observe
      (eval (H i) (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2
      (eval (H i) (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).1.length) =
    (∑ i ∈ worlds, weight i * observe
      (ARS_NativeOutcome.wrappers copy allocator CPH_Program.verifier a native1 native2 (native i))
      (ARS_NativeAccount.attempts (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a (native i))) := by
  have each := fun i => ARU_OriginalLaw.exact L copy allocator c err r native1 native2 hashv extraction a
    (native i) (H i) (n i) (syscall i) (consistent i)
  constructor
  · exact fun i => (each i).1
  · apply Finset.sum_congr rfl
    intro i member
    rw [(each i).2 Rat observe]

#print axioms original_law
end AspisR1.ARU_IndexedOriginalLaw
end
