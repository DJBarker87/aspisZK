import R1Z.PV_RunJoin_TrustFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_TrustSeparation
open PV_RunJoin_TrustBoundary PV_RunJoin_TrustFixtures

def trace (payload : Bool) : Observation Unit Nat Unit Nat Nat Bool where
  initial := errorWorld
  calls := [(errorWorld,.entropy ⟨0,by decide⟩ (errorWorld.entropy ⟨0,by decide⟩))]
  final := {errorWorld with entropyUsed := 1}
  filesystem := ⟨[],0,[]⟩
  payload := payload

def data (payload : Bool) :=
  model (fun _ _ => ()) (Equiv.refl Coins) (fun _ => trace payload)

theorem satisfies (payload : Bool) : PV_RunJoin_TrustItems (data payload) :=
  model_satisfies (fun _ _ => ()) (Equiv.refl Coins) _

/-- A checked interface countermodel, NOT a counterexample against shipped
privacy: native-to-extracted agreement alone does not prove agreement with
a specified security-model observation. That missing join is P-trace. -/
theorem trace_refinement_is_separate :
    ∃ d : Data Unit Nat Unit Nat Nat Unit Coins Unit Bool,
      PV_RunJoin_TrustItems d ∧ ∀ c, (d.extractedObservation c).payload ≠ true := by
  refine ⟨data false,satisfies false,?_⟩
  intro c
  exact Bool.false_ne_true

/-- Trust permits an actual OS error record. No availability condition is
silently introduced by the successful-byte law or the joint density field. -/
theorem no_implicit_availability :
    PV_RunJoin_TrustItems (data false) ∧
    ∀ c, (((data false).nativeObservation c).initial.entropy ⟨0,by decide⟩).2 = some () :=
  ⟨satisfies false,fun _ => rfl⟩

#print axioms satisfies
#print axioms trace_refinement_is_separate
#print axioms no_implicit_availability
end R1Z.PV_RunJoin_TrustSeparation
