import RPt_ARS_BudgetFromTotal
import RPz7_RawJ_InstalledBudget
import RPz8_RPx_ChargeBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_ReachedBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment SCE_Execution

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

/-- Budget only the adaptive calls actually reached, on their actual reply.
The quantifier does not impose promises on unreachable saved/heap inputs. -/
def ChoiceBound (Q1 : Nat) : Prop := ∀ H saved post final,
  (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 = ok (.Ok (saved,post,final)) →
  (eval H (a.second (eval H a.first).2 saved post final)).1.length ≤ Q1

/-- Every rejected prefix stays in the original account cost. -/
theorem issued (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ChoiceBound c hashv copy allocator id a Q1) (H : Bytes → State) :
    (eval H (account c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921 := by
  have head := prefixBound H
  have firstCost : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).1.length ≤ 1018 :=
    RawJ_InstalledBudget.first c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv copy allocator _ id _ _ H
  have secondCost : ∀ i, (eval H (secondCode c hashv allocator id i)).1.length ≤ 903 := by
    intro i
    exact RawJ_InstalledBudget.second c.adapter c.currentBase c.stageBase c.finish c.reserved
      c.query c.geometry c.boundaries c.std hashv allocator _ id _ _ _ H
  rw [account_def]
  simp only [eval_bind]
  cases reply : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 with
  | fail error => simp only [eval,List.length_append,List.length_nil]; omega
  | div => simp only [eval,List.length_append,List.length_nil]; omega
  | ok result =>
    cases result with
    | Err error => simp only [eval,List.length_append,List.length_nil]; omega
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      have choice := choiceBound H saved post final reply
      have tail := secondCost (eval H (a.second (eval H a.first).2 saved post final)).2
      simp only [eval_bind,eval,List.length_append,List.length_nil]
      omega

#print axioms issued
end AspisR1.ARS_ReachedBudget
end
