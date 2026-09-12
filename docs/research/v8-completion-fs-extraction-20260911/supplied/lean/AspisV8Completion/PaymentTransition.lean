/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import AspisV8Completion.TransferAmounts
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.PaymentTransition
open TransferAmounts

/-- Small executable state slice. Not the full forest/Token/Registry state.
The purpose is to avoid hiding conservation/replay prevention in a Valid field. -/
structure State where
  spent : Finset Nat
  outputs : List Nat
  cursor : Nat

structure Transfer where
  nullifier : Nat
  amounts : Amounts

def applyTransfer (state : State) (t : Transfer) : Option State :=
  if t.nullifier ∈ state.spent then none
  else if check t.amounts then some {
    spent := insert t.nullifier state.spent
    outputs := state.outputs ++ [t.amounts.recipient,t.amounts.change]
    cursor := state.cursor+2 }
  else none

theorem successful_effects (state out : State) (t : Transfer)
    (success : applyTransfer state t = some out) :
    t.nullifier ∉ state.spent ∧ valid t.amounts ∧
    out.spent = insert t.nullifier state.spent ∧
    out.outputs = state.outputs ++ [t.amounts.recipient,t.amounts.change] ∧
    out.cursor = state.cursor+2 := by
  unfold applyTransfer at success
  split at success
  · contradiction
  · rename_i fresh
    split at success
    · rename_i checked
      cases Option.some.inj success
      exact ⟨fresh, check_sound _ checked, rfl, rfl, rfl⟩
    · contradiction

theorem replay_rejected (state out : State) (t : Transfer)
    (success : applyTransfer state t = some out) : applyTransfer out t = none := by
  have effects := successful_effects state out t success
  simp [applyTransfer, effects.2.2.1]

#print axioms successful_effects
#print axioms replay_rejected
end AspisV8Completion.PaymentTransition
