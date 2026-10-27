import RPz8_ARW_AdmittedQueries
import RPz8_ARV_Constant
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_DisconnectedAdmissions
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
theorem obstruction {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv H)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    ∃ b : Adversary A,
      (∀ world, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier b world).length = 0) ∧
      (∀ world, ART_AdversaryWork.work (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier b world = 0) ∧
      SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier b)).2 = true ∧
      ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv b H) := by
  let i := (eval H a.first).2
  let j := (eval H (a.second i n.entry.saved n.entry.post1 n.entry.final1)).2
  let b := ARV_Constant.adversary i (ARV_Constant.poison j)
  refine ⟨b,?_,?_,?_,?_⟩
  · intro world
    unfold ARW_Induced.issued b ARV_Constant.adversary
    simp only [eval]
    split <;> rfl
  · intro world
    unfold ART_AdversaryWork.work b ARV_Constant.adversary
    simp only [eval]
    split <;> rfl
  · exact ARV_Constant.accepted copy allocator c err r native1 native2 hashv extraction H syscall i j
      n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2
      n.entry.accepted1 n.entry.accepted2
  · exact ARV_Constant.no_support L copy allocator c err r native1 native2 hashv i j H

#print axioms obstruction
end AspisR1.ARW_DisconnectedAdmissions
end
