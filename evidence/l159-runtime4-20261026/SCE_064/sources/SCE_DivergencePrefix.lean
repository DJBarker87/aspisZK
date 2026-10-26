import SCE_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_DivergencePrefix
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment SCE_Execution
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)

/-- Every attempted first-wrapper query is retained; the adaptive second
choice is not invoked after this result. No rejected prefix is erased. -/
theorem execution 
    (failed : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 = .div) :
    eval H (account c hashv copy allocator id a) =
      ((eval H a.first).1 ++ (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1,
        ((eval H a.first).2,.div,none)) := by
  rw [account_def]
  simp only [eval_bind,failed,eval,List.append_nil]

#print axioms execution
end AspisR1.SCE_DivergencePrefix
end
