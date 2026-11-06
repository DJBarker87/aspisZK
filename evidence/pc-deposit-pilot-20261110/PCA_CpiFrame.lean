import PCA_State
set_option autoImplicit false
namespace PCA
structure AccountView where
  owner : Bytes
  data : Bytes
  lamports : Nat

def view (s : PCA_State) (a : Nat) : AccountView :=
  let account := s.loans.state.accounts a
  ⟨account.owner,(s.loans.state.cells account.data).payload.bytes,
    (s.loans.state.cells account.lamports).payload.money⟩

/-- PENDING LEAD RULING. This is deliberately a Prop hypothesis of intermediates,
never an axiom, instance or root premise. No token/system semantics, success,
read-only behavior or cross-transaction persistence is asserted. -/
structure PCA_CpiFrameCandidate (before after : PCA_State) (infos : List Nat)
    (calleeFinal : Nat → AccountView) : Prop where
  unpassed : ∀ a, a < before.accountCount → a ∉ infos →
    view after a = view before a
  reflected : ∀ a, a ∈ infos → view after a = calleeFinal a

/-- Exact necessary frame for the protected lane/page. This conclusion cannot
be obtained just by reapplying entry counterZero after the call. -/
theorem protected_view (before after : PCA_State) (infos : List Nat)
    (calleeFinal : Nat → AccountView) (candidate : PCA_CpiFrameCandidate before after infos calleeFinal)
    (account : Nat) (bound : account < before.accountCount) (separate : account ∉ infos) :
    view after account = view before account := candidate.unpassed account bound separate

/-- A changed unpassed view contradicts the proposed interface. This is an
abstract logical obstruction, not a transaction shape or a reachable exploit. -/
theorem changed_unpassed_excludes_candidate (before after : PCA_State) (infos : List Nat)
    (calleeFinal : Nat → AccountView) (account : Nat) (bound : account < before.accountCount)
    (separate : account ∉ infos) (changed : view after account ≠ view before account) :
    ¬ PCA_CpiFrameCandidate before after infos calleeFinal := by
  intro candidate
  exact changed (candidate.unpassed account bound separate)

#print axioms protected_view
#print axioms changed_unpassed_excludes_candidate
end PCA
