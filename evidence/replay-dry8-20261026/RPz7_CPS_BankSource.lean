import RPz7_CPP_OracleSource
import RPz7_CPP_BankHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_BankSource
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Invoke the actual CPP source wrapper on the same bank-adjusted layout.
Foreign writes, funding and cleanup remain the explicit CPP bank model;
this definition does not assert deployed executor/source correspondence. -/
def step {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (bank : Bank) (action : Action A) : Program Bytes State (Bank × S2X.AccountEvent) :=
  match action with
  | .invoke input => bind (CPP_Oracle.program c hashv copy allocator id bank.cells (invocation bank input))
      (fun effect => .done (⟨effect.1,bank.lamports⟩,effect.2.1))
  | .foreign caller key value coins => .done (CPP_BankState.apply n1 n2 copy allocator id bank (.foreign caller key value coins))
  | .credit key amount => .done (CPP_BankState.apply n1 n2 copy allocator id bank (.credit key amount))
  | .reap key => .done (CPP_BankState.apply n1 n2 copy allocator id bank (.reap key))
  | .rollback => .done (bank,.rollback)

theorem step_effect {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (bank : Bank) (action : Action A) :
    (eval H (step c hashv n1 n2 copy allocator id bank action)).2 =
      CPP_BankState.apply n1 n2 copy allocator id bank action := by
  cases action with
  | invoke input =>
    simp only [step,eval_bind,eval]
    rw [CPP_OracleSource.effect c hashv copy allocator id bank.cells (invocation bank input)
      n1 n2 extraction sha256 H p1 syscall]
    rfl
  | foreign caller key value coins => rfl
  | credit key amount => rfl
  | reap key => rfl
  | rollback => rfl

#print axioms step_effect
end AspisR1.CPS_BankSource
end
