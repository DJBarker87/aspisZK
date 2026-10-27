import ARU_Factory
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_IndexedFactory
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
    (n : ∀ i, ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a (native i))
    (consistent : ∀ i, ARS_AccountReplay.Consistent
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) (native i) (H i))
    (worlds : Finset I) (weight : I → Rat)
    (observe : List (Bytes × State) × GExq_AccountExperiment.Outcome A → Rat) :
    (∀ i, Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a (H i))) ∧
    (∑ i ∈ worlds, weight i * observe (eval (H i)
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a))) =
    (∑ i ∈ worlds, weight i * observe (eval (native i)
      (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a))) := by
  constructor
  · intro i
    exact ARU_Factory.deployed L copy allocator c err r native1 native2 hashv extraction a (native i) (H i) (n i) (consistent i)
  · apply Finset.sum_congr rfl
    intro i member
    rw [ARS_AccountReplay.replay _ (native i) (H i) (consistent i)]

#print axioms original_law
end AspisR1.ARU_IndexedFactory
end
