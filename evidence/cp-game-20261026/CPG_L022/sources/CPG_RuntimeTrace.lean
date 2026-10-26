import CPP_BankHistory
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPG_RuntimeTrace
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPP_BankState Hist_Store
attribute [local instance] Classical.propDecidable

variable {A : Type}
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

/-- Checkpoint projection of one runtime action, with its actual bank states
and event. Constructors expose the authority, funding and boundary checks.
This is the existing CPP action domain, not an axiom about arbitrary validator
transitions or an independently certified deployed validator implementation. -/
inductive Step : Bank → Action A → Bank → S2X.AccountEvent → Prop where
  | invoke (bank : Bank) (input : CPP_Invocation.Invocation A) :
      let effect := CPP_Invocation.native n1 n2 copy allocator id bank.cells (invocation bank input)
      Step bank (.invoke input) ⟨effect.1,bank.lamports⟩ effect.2.1
  | foreign (bank : Bank) (caller : S2W_ExtractionBoundary.Program) (key : Nat)
      (value : Cell) (coins : Nat)
      (authorized : caller ≠ id ∧ (bank.cells key).owner = caller ∧
        (value.owner = caller ∨ Hir_ProvenanceModel.Zero value.data)) :
      Step bank (.foreign caller key value coins)
        ⟨Hist_Store.put bank.cells key value,S2Trust.put bank.lamports key coins⟩
        (.committedWrite key (MultiproofConeCanonical.bytesOf value.data.val))
  | foreignRejected (bank : Bank) (caller : S2W_ExtractionBoundary.Program) (key : Nat)
      (value : Cell) (coins : Nat)
      (rejected : ¬ (caller ≠ id ∧ (bank.cells key).owner = caller ∧
        (value.owner = caller ∨ Hir_ProvenanceModel.Zero value.data))) :
      Step bank (.foreign caller key value coins) bank .rollback
  | credit (bank : Bank) (key amount : Nat) :
      Step bank (.credit key amount)
        ⟨bank.cells,S2Trust.put bank.lamports key (bank.lamports key+amount)⟩ .rollback
  | reap (bank : Bank) (key : Nat) (zero : bank.lamports key = 0) :
      Step bank (.reap key) ⟨Hist_Store.put bank.cells key absent,bank.lamports⟩ (.committedWrite key [])
  | live (bank : Bank) (key : Nat) (positive : bank.lamports key ≠ 0) :
      Step bank (.reap key) bank .rollback
  | rollback (bank : Bank) : Step bank .rollback bank .rollback

/-- Every recorded intermediate bank and event is threaded through the trace.
No endpoint equality or history-protection conclusion is a constructor field. -/
inductive Executes : Bank → List (Action A) → Bank → List S2X.AccountEvent → Prop where
  | nil (bank : Bank) : Executes bank [] bank []
  | cons {initial middle final : Bank} {action : Action A} {rest : List (Action A)}
      {event : S2X.AccountEvent} {events : List S2X.AccountEvent}
      (head : Step n1 n2 copy allocator id initial action middle event)
      (tail : Executes middle rest final events) :
      Executes initial (action :: rest) final (event :: events)

variable {n1 n2 copy allocator id}

theorem step_effect {initial final : Bank} {action : Action A} {event : S2X.AccountEvent}
    (step : Step n1 n2 copy allocator id initial action final event) :
    CPP_BankState.apply n1 n2 copy allocator id initial action = (final,event) := by
  cases step with
  | invoke => rfl
  | foreign bank caller key value coins authorized => exact if_pos authorized
  | foreignRejected bank caller key value coins rejected => exact if_neg rejected
  | credit => rfl
  | reap bank key zero => exact if_pos zero
  | live bank key positive => exact if_neg positive
  | rollback => rfl

theorem result {initial final : Bank} {actions : List (Action A)} {events : List S2X.AccountEvent}
    (trace : Executes n1 n2 copy allocator id initial actions final events) :
    CPP_BankHistory.run n1 n2 copy allocator id initial actions = (final,events) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
    simp only [CPP_BankHistory.run,step_effect head,ih]

variable (n1 n2 copy allocator id)

theorem step_exists (bank : Bank) (action : Action A) :
    Step n1 n2 copy allocator id bank action
      (CPP_BankState.apply n1 n2 copy allocator id bank action).1
      (CPP_BankState.apply n1 n2 copy allocator id bank action).2 := by
  cases action with
  | invoke input => exact Step.invoke bank input
  | foreign caller key value coins =>
    by_cases allowed : caller ≠ id ∧ (bank.cells key).owner = caller ∧
        (value.owner = caller ∨ Hir_ProvenanceModel.Zero value.data)
    · simpa only [CPP_BankState.apply,if_pos allowed] using Step.foreign bank caller key value coins allowed
    · simpa only [CPP_BankState.apply,if_neg allowed] using Step.foreignRejected bank caller key value coins allowed
  | credit key amount => exact Step.credit bank key amount
  | reap key =>
    by_cases zero : bank.lamports key = 0
    · simpa only [CPP_BankState.apply,if_pos zero] using Step.reap bank key zero
    · simpa only [CPP_BankState.apply,if_neg zero] using Step.live bank key zero
  | rollback => exact Step.rollback bank

theorem executes (initial : Bank) (actions : List (Action A)) :
    Executes n1 n2 copy allocator id initial actions
      (CPP_BankHistory.run n1 n2 copy allocator id initial actions).1
      (CPP_BankHistory.run n1 n2 copy allocator id initial actions).2 := by
  induction actions generalizing initial with
  | nil => exact Executes.nil initial
  | cons action rest ih => exact Executes.cons (step_exists n1 n2 copy allocator id initial action) (ih _)

#print axioms step_effect
#print axioms result
#print axioms step_exists
#print axioms executes
end AspisR1.CPG_RuntimeTrace
end
