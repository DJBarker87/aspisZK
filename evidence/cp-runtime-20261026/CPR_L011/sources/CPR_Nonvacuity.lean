import CPR_CommittedLoad
import CPP_BankNonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPR_Nonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers CPP_BankState CPR_Persistence
open Hist_Nonvacuity (key original changed)

/-- An operational interpretation satisfying the proposed law by construction.
This proves consistency of the law, not correspondence with deployed Agave. -/
def canonical {Tx Key : Type} (before tentative : Tx → Key → Image)
    (success : Tx → Bool) (predecessor : Tx → Tx) : Tx → Key → Option Image :=
  fun u key => visible (if success (predecessor u) then tentative (predecessor u) key else before (predecessor u) key)

theorem canonical_law {Tx Key : Type} (before tentative : Tx → Key → Image)
    (success : Tx → Bool) (predecessor : Tx → Tx) :
    TwoTransactionLaw (fun t u => predecessor u = t) (fun _ _ => True)
      before tentative success (canonical before tentative success predecessor) := by
  intro t u adjacent key eligible
  simp only [canonical,adjacent]

/-- Nonempty source-model suffix: credit, foreign write, genuine zero cleanup
on another key, attempted cleanup on the protected positive key. -/
theorem nonempty_suffix
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) :
    CPP_BankNonvacuity.actions ≠ [] ∧
    let after := (CPP_BankHistory.run n1 n2 copy allocator (key 0#u8)
      CPP_BankNonvacuity.initial CPP_BankNonvacuity.actions).1
    visible (snapshot after 0) = some (snapshot after 0) ∧
    visible (snapshot after 1) = none ∧
    after.cells 0 = original 0 := by
  have reached := CPP_BankNonvacuity.reached n1 n2 copy allocator
  refine ⟨List.cons_ne_nil _ _,?_,?_,reached.1⟩
  · apply if_neg
    change (CPP_BankHistory.run n1 n2 copy allocator (key 0#u8)
      CPP_BankNonvacuity.initial CPP_BankNonvacuity.actions).1.lamports 0 ≠ 0
    rw [reached.2.1]
    omega
  · have permitted : key 1#u8 ≠ key 0#u8 ∧ (original 1).owner = key 1#u8 ∧
        (changed.owner = key 1#u8 ∨ Hir_ProvenanceModel.Zero changed.data) :=
      ⟨Hist_Nonvacuity.different,by simp [original],Or.inl rfl⟩
    apply if_pos
    simp [snapshot,CPP_BankNonvacuity.initial,CPP_BankNonvacuity.actions,
      CPP_BankHistory.run,CPP_BankState.apply,permitted,S2Trust.put,Hist_Store.put]

/-- Failure discards tentative writes AND credits. This model has real actions,
not a premise asserting that an observed output already equals saved bytes. -/
theorem parent_failure
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) :
    CPR_AtomicBank.run n1 n2 copy allocator (key 0#u8)
      CPP_BankNonvacuity.initial CPP_BankNonvacuity.actions false =
      (CPP_BankNonvacuity.initial,[.rollback]) := rfl

#print axioms canonical_law
#print axioms nonempty_suffix
#print axioms parent_failure
end AspisR1.CPR_Nonvacuity
end
