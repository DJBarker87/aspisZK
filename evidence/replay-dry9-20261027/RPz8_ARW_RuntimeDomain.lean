import RPz8_ARW_DisconnectedAdmissions
import RPz8_ART_Runtime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_RuntimeDomain
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
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) (Q0 Q1 : Nat) :
    ∃ (b : Adversary A) (run : F3T_Experiment.RunView),
      (∀ world, (eval world (ARW_Induced.program native1 copy allocator CPH_Program.verifier b)).1.length ≤ Q0+Q1) ∧
      (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier b)).2 = some run ∧
      run.2.2 = true ∧
      ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv b H) := by
  obtain ⟨b,zero,work,yes,unsupported⟩ := ARW_DisconnectedAdmissions.obstruction L copy allocator c err r
    native1 native2 hashv extraction a H syscall n
  let v := eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
    hashv copy allocator CPH_Program.verifier b)
  let run : F3T_Experiment.RunView :=
    (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input (FIp_Install.configuration err c r)
      (submitted v.2.1)),accepted v.2))
  refine ⟨b,run,?_,?_,yes,unsupported⟩
  · intro world
    rw [ARW_Induced.queries,zero]
    exact Nat.zero_le _
  · rw [ART_Runtime.eval_runtime]

#print axioms obstruction
end AspisR1.ARW_RuntimeDomain
end
