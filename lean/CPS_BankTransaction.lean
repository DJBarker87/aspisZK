import CPS_BankRecorder
import CPS_ParentStatus
import CPR_AtomicBank
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_BankTransaction
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {A B F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- Atomic projection of the complete supplied source action list and FINAL
parent reply. Association of these inputs with a validator trace is not asserted.
The reply remains visible, including errors/divergence, after settlement. -/
def program (bank : Bank) (actions : List (Action A)) (reply : CPP_Atomic.Reply B) :
    Program Bytes State ((Bank × List S2X.AccountEvent) × CPP_Atomic.Reply B) :=
  bind (CPS_BankRecorder.program c hashv n1 n2 copy allocator id bank actions) fun raw =>
    .done (CPR_AtomicBank.settle bank raw (CPS_ParentStatus.success reply),reply)

theorem evaluation (H : Bytes → State) (bank : Bank) (actions : List (Action A))
    (reply : CPP_Atomic.Reply B) :
    eval H (program c hashv n1 n2 copy allocator id bank actions reply) =
      ((eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id bank actions)).1,
       (CPR_AtomicBank.settle bank
         (eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id bank actions)).2
         (CPS_ParentStatus.success reply),reply)) := by
  simp only [program,eval_bind,eval,List.append_nil]

theorem source_result
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (bank : Bank) (actions : List (Action A)) (reply : CPP_Atomic.Reply B) :
    (eval H (program c hashv n1 n2 copy allocator id bank actions reply)).2 =
      (CPR_AtomicBank.run n1 n2 copy allocator id bank actions (CPS_ParentStatus.success reply),reply) := by
  rw [evaluation,CPS_BankRecorder.result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall]
  rfl

/-- Settlement changes neither the reached queries nor the final reply. -/
theorem query_frame (H : Bytes → State) (bank : Bank) (actions : List (Action A))
    (reply : CPP_Atomic.Reply B) :
    (eval H (program c hashv n1 n2 copy allocator id bank actions reply)).1 =
      (eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id bank actions)).1 := by
  rw [evaluation]

theorem failed (H : Bytes → State) (bank : Bank) (actions : List (Action A))
    (reply : CPP_Atomic.Reply B) (status : CPS_ParentStatus.success reply = false) :
    (eval H (program c hashv n1 n2 copy allocator id bank actions reply)).2 =
      ((bank,[.rollback]),reply) := by
  rw [evaluation,status]
  rfl

#print axioms evaluation
#print axioms source_result
#print axioms query_frame
#print axioms failed
end AspisR1.CPS_BankTransaction
end
