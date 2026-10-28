import R1Z.PV_RunJoin_ResultTransport
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PairElimination

/-- Symbolic product elimination; avoids normalization through opaque source
records while transporting the emitted monadic continuations. -/
theorem cases_pair {A B C : Type} (pair : A × B) (continuation : A → B → C) :
    Prod.casesOn pair continuation = continuation pair.1 pair.2 := by
  cases pair
  rfl

#print axioms cases_pair
end R1Z.PV_RunJoin_PairElimination
