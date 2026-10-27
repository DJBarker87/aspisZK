import ARS_Chronology
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_BudgetFromTotal
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_Execution

/-- Correct direction for an actual per-execution budget: full issued work
bounds the actual adaptive choice, including repeats. It does not establish a
bound for unreachable calls to a.second with arbitrary saved/post/final values. -/
theorem choice {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 = ok (.Ok (saved,post,final)))
    (Q : Nat) (total : (eval H (account c hashv copy allocator id a)).1.length ≤ Q) :
    (eval H (a.second (eval H a.first).2 saved post final)).1.length ≤ Q := by
  rw [accepted_eval c hashv copy allocator id a H saved post final first] at total
  simp only [List.length_append] at total
  omega

/-- A total original budget also bounds the first choice on every path. -/
theorem first {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State) (Q : Nat)
    (total : (eval H (account c hashv copy allocator id a)).1.length ≤ Q) :
    (eval H a.first).1.length ≤ Q := by
  rw [account_def] at total
  simp only [AspisV8R19.OracleProgramOps.eval_bind,List.length_append] at total
  omega

#print axioms choice
#print axioms first
end AspisR1.ARS_BudgetFromTotal
end
