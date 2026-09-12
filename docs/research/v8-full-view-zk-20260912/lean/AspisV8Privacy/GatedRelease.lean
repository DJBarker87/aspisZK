import AspisV8Privacy.FiniteGames

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM.
A real prover-side rank gate may avoid releasing bad-schedule proofs. It is
not enough to delete bad executions from the sample space: gate/abort law
must also match. This transport theorem allows DIFFERENT unreleased views.
It does not assert that the selected V8 prover actually runs any such gate.
-/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section
variable {C D V : Type*}

def gatedRelease (gate : V → Bool) (v : V) : Option V :=
  if gate v = true then some v else none

/-- The coin bijection must preserve whether publication occurs, as well as
matching the full released view when it does. Abort is an explicit result. -/
theorem gated_release_transport
    (f : C → V) (g : D → V) (e : C ≃ D) (gate : V → Bool)
    (gateSame : ∀ c, gate (g (e c)) = gate (f c))
    (goodViewSame : ∀ c, gate (f c) = true → g (e c) = f c) (c : C) :
    gatedRelease gate (g (e c)) = gatedRelease gate (f c) := by
  by_cases good : gate (f c) = true
  · rw [goodViewSame c good]
  · simp [gatedRelease, gateSame c, good]

/-- Does not require equality of the private candidate body on a rejected
trial. A source-proved gate-preserving coin transport is still necessary. -/
theorem gated_release_same_uniform_law
    [Fintype C] [Fintype D] [Nonempty C] [Nonempty D]
    (f : C → V) (g : D → V) (e : C ≃ D) (gate : V → Bool)
    (gateSame : ∀ c, gate (g (e c)) = gate (f c))
    (goodViewSame : ∀ c, gate (f c) = true → g (e c) = f c) :
    SameUniformLaw (gatedRelease gate ∘ f) (gatedRelease gate ∘ g) := by
  apply sameUniformLaw_of_coinEquiv _ _ e
  intro c
  exact gated_release_transport f g e gate gateSame goodViewSame c

#print axioms gated_release_transport
#print axioms gated_release_same_uniform_law
end
end AspisV8Privacy
