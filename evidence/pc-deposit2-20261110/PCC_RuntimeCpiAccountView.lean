import PCA_CpiFrame
set_option autoImplicit false
namespace PCC
open PCA
/-- ADDED-LEAD-20261110 (c-a), returning Pool invokes only. Clause 1 is
keyed on instruction metas, not the passed infos. No guard/counter frame. -/
structure RuntimeCpiAccountView (before after : PCA_State)
    (instruction : Instruction) (infos : List Nat)
    (calleeFinal : Bytes → AccountView) : Prop where
  unmentioned : ∀ a, a < before.accountCount →
    (∀ accountMeta ∈ instruction.metas, (before.loans.state.accounts a).key ≠ accountMeta.key.toList) →
    view after a = view before a
  reflected : ∀ a, a < before.accountCount → a ∈ infos →
    (∃ accountMeta ∈ instruction.metas, (before.loans.state.accounts a).key = accountMeta.key.toList) →
    view after a = calleeFinal (before.loans.state.accounts a).key

/-- A caller must prove exclusion from M on its reached instruction. -/
theorem protected_view (before after : PCA_State) (instruction : Instruction)
    (infos : List Nat) (calleeFinal : Bytes → AccountView)
    (runtime : RuntimeCpiAccountView before after instruction infos calleeFinal)
    (a : Nat) (bound : a < before.accountCount)
    (absent : ∀ m ∈ instruction.metas, (before.loans.state.accounts a).key ≠ m.key.toList) :
    view after a = view before a := runtime.unmentioned a bound absent

/-- Passed values remain unconstrained by this theorem; the row reflects them. -/
theorem passed_view (before after : PCA_State) (instruction : Instruction)
    (infos : List Nat) (calleeFinal : Bytes → AccountView)
    (runtime : RuntimeCpiAccountView before after instruction infos calleeFinal)
    (a : Nat) (bound : a < before.accountCount) (passed : a ∈ infos)
    (mentioned : ∃ m ∈ instruction.metas, (before.loans.state.accounts a).key = m.key.toList) :
    view after a = calleeFinal (before.loans.state.accounts a).key :=
  runtime.reflected a bound passed mentioned
#print axioms protected_view
#print axioms passed_view
end PCC
