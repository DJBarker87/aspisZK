import RPz7_CPS_BankSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPS_BankRecorder
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- One state-threaded source observation, not independently selected cuts. -/
def program (bank : Bank) : List (Action A) → Program Bytes State (Bank × List S2X.AccountEvent)
  | [] => .done (bank,[])
  | action :: rest => bind (CPS_BankSource.step c hashv n1 n2 copy allocator id bank action) fun head =>
      bind (program head.1 rest) fun tail => .done (tail.1,head.2 :: tail.2)

theorem result
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (bank : Bank) (actions : List (Action A)) :
    (eval H (program c hashv n1 n2 copy allocator id bank actions)).2 =
      CPP_BankHistory.run n1 n2 copy allocator id bank actions := by
  induction actions generalizing bank with
  | nil => rfl
  | cons action rest ih =>
    simp only [program,eval_bind,eval]
    rw [CPS_BankSource.step_effect c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall,
      ih]
    rfl

/-- Ordered event identity is now derived for the source/bank model. Physical
association with a validator trace is still a separate unproved obligation. -/
theorem events
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (bank : Bank) (actions : List (Action A)) :
    (eval H (program c hashv n1 n2 copy allocator id bank actions)).2.2 =
      (CPP_BankHistory.run n1 n2 copy allocator id bank actions).2 :=
  congrArg Prod.snd (result c hashv n1 n2 copy allocator id extraction sha256 H p1 syscall bank actions)

#print axioms result
#print axioms events
end AspisR1.CPS_BankRecorder
end
