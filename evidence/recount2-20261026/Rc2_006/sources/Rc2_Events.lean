import CPS_SourceTop
import CPP_AtomicSource
import CPR_AtomicBank
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc2_Events
open Aeneas Aeneas.Std Result
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- The unconditional source-event part of CPS_SourceTop.correlated. No
runtime loader law, physical association or protected history is asserted.
The saved vector is the actual accepted TX1 return at the enclosing root. -/
def Facts {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (H : Bytes → State) (saved : alloc.vec.Vec U8) : Prop :=
  (∀ (initial : CPP_BankState.Bank) (key : Nat) (actions : List (CPP_BankState.Action A)),
    (eval H (CPS_BankRecorder.program c hashv n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy initial key saved) actions)).2.2 =
    (CPP_BankHistory.run n1 n2 copy allocator id
      (CPR_SourceBank.afterCopy initial key saved) actions).2) ∧
  (∀ (initial : Hist_Store.Store) (code : CPP_Schedule.Schedule A (CPP_Atomic.Reply Unit)),
    eval H (CPP_Atomic.program n1 copy allocator id c hashv initial code) =
      ((eval H (CPP_Schedule.program n1 copy allocator id c hashv initial code)).1,
        CPP_Atomic.run n1 n2 copy allocator id H initial code)) ∧
  (∀ (initial : CPP_BankState.Bank) (actions : List (CPP_BankState.Action A)),
    CPR_AtomicBank.run n1 n2 copy allocator id initial actions false = (initial,[.rollback]))

theorem derive {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (saved : alloc.vec.Vec U8) : Facts c hashv n1 n2 copy allocator id H saved := by
  refine ⟨?_,?_,?_⟩
  · intro initial key actions
    exact CPS_BankRecorder.events c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall _ actions
  · intro initial code
    have value := CPP_AtomicSource.native c hashv n1 copy allocator id initial code n2 extraction sha256 H p1 syscall
    have trace := CPP_AtomicSource.evaluation c hashv n1 copy allocator id initial code H
    apply Prod.ext
    · exact congrArg (fun x => x.1) trace
    · exact value
  · intro initial actions
    rfl

#print axioms derive
end AspisR1.Rc2_Events
end
