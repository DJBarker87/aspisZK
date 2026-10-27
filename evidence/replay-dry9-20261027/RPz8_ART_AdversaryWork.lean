import RPz8_ART_PrefixCoupling
import RPz8_ART_FirstProjection
import RPz7_RawJ_InstalledBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_AdversaryWork
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment ARS_NativeAccount ART_PartialAccount

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

/-- Original adversary work on the reached phase only. Both prefixes include
repeats. Neither failed wrapper calls nor nonexistent TX2 choices are erased. -/
def work (H : Bytes → State) : Nat :=
  (eval H a.first).1.length +
    match (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 with
    | .ok (.Ok (saved,post,final)) =>
      (eval H (a.second (eval H a.first).2 saved post final)).1.length
    | _ => 0

def Bound (Q : Nat) : Prop := ∀ H, work c hashv copy allocator id a H ≤ Q

theorem first (Q : Nat) (bound : Bound c hashv copy allocator id a Q) (H : Bytes → State) :
    (eval H a.first).1.length ≤ Q := by
  have total := bound H
  unfold work at total
  omega

/-- Per-phase bounds yield Q0+Q1, not Q0 or an extra 34 sampler allowance. -/
theorem phases (Q0 Q1 : Nat) (head : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choice : ∀ H saved post final,
      (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 =
        ok (.Ok (saved,post,final)) →
      (eval H (a.second (eval H a.first).2 saved post final)).1.length ≤ Q1) :
    Bound c hashv copy allocator id a (Q0+Q1) := by
  intro H
  unfold work
  cases reply : (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 with
  | fail error => simpa only [Nat.add_zero] using (head H).trans (Nat.le_add_right _ _)
  | div => simpa only [Nat.add_zero] using (head H).trans (Nat.le_add_right _ _)
  | ok result =>
    cases result with
    | Err error => simpa only [Nat.add_zero] using (head H).trans (Nat.le_add_right _ _)
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      exact Nat.add_le_add (head H) (choice H saved post final reply)

#print axioms first
#print axioms phases
end AspisR1.ART_AdversaryWork
end
