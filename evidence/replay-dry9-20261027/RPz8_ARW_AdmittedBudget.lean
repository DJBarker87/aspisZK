import RPz8_ARW_AdmittedQueries
import RPz8_ARW_LocalBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_AdmittedBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
theorem issued {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) (Q0 Q1 : Nat)
    (queries : ∀ world, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a world).length ≤ Q0+Q1) :
    ART_AdversaryWork.work (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H ≤ Q0+Q1 ∧
    (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).1.length ≤ Q0+Q1+1921 := by
  have bound := queries H
  rw [ARW_AdmittedQueries.admitted L copy allocator c err r native1 native2 hashv extraction a H n] at bound
  exact ⟨bound,ARW_LocalBudget.issued (FIp_Install.configuration err c r)
    hashv copy allocator CPH_Program.verifier a (Q0+Q1) H bound⟩

#print axioms issued
end AspisR1.ARW_AdmittedBudget
end
