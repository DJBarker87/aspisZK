import ARV_PaddingSupport
import ARV_PaddingWork
import ARV_FirstPartial
import ARU_PartialAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_NativeCostGap
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open GExq_AccountExperiment SCE_Experiment

theorem obstruction {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a native) (address : Bytes) (Q : Nat)
    (queries : ∀ H, (eval H (submission a)).1.length ≤ Q) :
    ∃ b : Adversary A,
      submission b = submission a ∧
      (∀ H, (eval H (submission b)).1.length ≤ Q) ∧
      Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv b native) ∧
      SCE_Experiment.accepted (eval native (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier b)).2 = true ∧
      Q < ART_AdversaryWork.work (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier b native ∧
      ¬ ART_AdversaryWork.Bound (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier b Q := by
  let b := ARQ_ChoiceCoverage.pad a address (Q+1)
  have same : submission b = submission a := ARQ_ChoiceCoverage.submitted a address (Q+1)
  obtain ⟨padded⟩ := ARV_PaddingSupport.original L copy allocator c err r native1 native2 hashv a native address (Q+1) n
  have yes := (ARU_PartialAccepted.accepted L copy allocator c err r native1 native2 hashv extraction b native padded).1
  have first := ARV_FirstPartial.accepted L copy allocator c err r native1 native2 hashv extraction a native n
  have work := ARV_PaddingWork.exact (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a
    address (Q+1) native n.entry.saved n.entry.post1 n.entry.final1 first
  have large : Q < ART_AdversaryWork.work (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier b native := by
    dsimp only [b]
    rw [work]
    omega
  refine ⟨b,same,?_,⟨padded⟩,yes,large,?_⟩
  · intro H; rw [same]; exact queries H
  · intro total
    exact Nat.not_le_of_gt large (total native)

#print axioms obstruction
end AspisR1.ARV_NativeCostGap
end
