import SCE_CompleteSubmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_AccountBound
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)

include prefixBound choiceBound

theorem issued (H : Bytes → State) :
    (eval H (account c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921 := by
  have bounded := SCE_CompleteSubmission.queries c hashv copy allocator id a Q0 Q1 prefixBound choiceBound H
  rw [SCE_CompleteSubmission.evaluation] at bounded
  exact bounded

theorem observed (H : Bytes → State) :
    (eval H (runtime c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921 := by
  rw [runtime_eval]
  exact issued c hashv copy allocator id a Q0 Q1 prefixBound choiceBound H

#print axioms issued
#print axioms observed
end AspisR1.SCE_AccountBound
end
