import ARW_AdmittedQueries
import ARX_AdmittedRuntime
import ARV_Constant
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_OldClassPoison
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
theorem differs {W A C Tx : Type} (L : Library W (Nat → Record))
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
      (∃ choose : FirstInputs A → SecondInputs A, b.second = fun i _ _ _ => .done (choose i)) ∧
      (∃ run, (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r)
        hashv copy allocator CPH_Program.verifier b)).2 = some run ∧ run.2.2 = true) ∧
      (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv b)).2 = none := by
  let i := (eval H a.first).2
  let j := (eval H (a.second i n.entry.saved n.entry.post1 n.entry.final1)).2
  let b := ARV_Constant.adversary i (ARV_Constant.poison j)
  have yes := ARV_Constant.accepted copy allocator c err r native1 native2 hashv extraction H syscall i j
    n.entry.saved n.entry.post1 n.entry.post2 n.entry.final1 n.entry.final2 n.entry.accepted1 n.entry.accepted2
  let v := eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
    hashv copy allocator CPH_Program.verifier b)
  let run : F3T_Experiment.RunView := (v.1,(F3T_Canon.canonInput (F3T_ByteCarrier.input
    (FIp_Install.configuration err c r) (submitted v.2.1)),accepted v.2))
  refine ⟨b,⟨fun _ => ARV_Constant.poison j,rfl⟩,⟨run,?_,yes⟩,?_⟩
  · rw [ART_Runtime.eval_runtime]
  · exact ARX_AdmittedRuntime.excludes_poison L copy allocator c err r native1 native2 hashv extraction i j H

#print axioms differs
end AspisR1.ARX_OldClassPoison
end
