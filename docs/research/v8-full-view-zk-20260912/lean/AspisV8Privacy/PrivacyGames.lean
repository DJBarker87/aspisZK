import AspisV8Privacy.FiniteGames
import Mathlib.Algebra.Order.Field.Rat

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM.
A precise target definition, NOT a theorem. Existence of a witness-dependent
coin translation proves at most WI; the simulator below gets NO witness.
Computational efficiency and source/ROM instantiation remain explicit gates.
-/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section
variable {C D V X W A : Type*}
variable [Fintype C] [Fintype D] [Nonempty C] [Nonempty D]

def EventAdvantage (real : C → V) (sim : D → V) (event : V → Bool) : ℚ :=
  |uniformProbability (event ∘ real) true - uniformProbability (event ∘ sim) true|

def EventDistanceBound (real : C → V) (sim : D → V) (epsilon : ℚ) : Prop :=
  ∀ event, EventAdvantage real sim event ≤ epsilon

/-- Ideal finite-game STATISTICAL target. For a fixed concrete hash/PRG,
use the resource-bounded computational target below instead.
A single simulator family, selected before witnesses. The observer A
must be a bounded interactive strategy in the eventual source instantiation;
not a fixed transcript secretly chosen using the witness or masks. -/
def FullViewSimulationGoal
    (valid : X → W → Prop)
    (real : A → X → W → C → V)
    (sim : A → X → D → V)
    (allowed : A → Prop) (epsilon : ℚ) : Prop :=
  ∀ a, allowed a → ∀ x w, valid x w →
    EventDistanceBound (real a x w) (sim a x) epsilon

/-- Runtime obligations cannot be omitted by a noncomputable choice of a
witness/preimage. This is only a place to state a concrete future cost bound. -/
def SimulatorCostGoal (cost : A → X → D → Nat) (budget : A → X → Nat) : Prop :=
  ∀ a x coins, cost a x coins ≤ budget a x

/-- Explicit restricted tests for a computational claim. The final adapter
must define this class by an actual executable resource model, not by whether
a test happens to satisfy the desired advantage bound. -/
def ComputationalDistanceBound
    (tests : (V → Bool) → Prop) (real : C → V) (sim : D → V)
    (epsilon : ℚ) : Prop :=
  ∀ event, tests event → EventAdvantage real sim event ≤ epsilon

/-- Fixed-hash computational target; still only a definition. The public
statement x includes the explicitly allowed public leakage. -/
def ComputationalFullViewSimulationGoal
    (valid : X → W → Prop) (real : A → X → W → C → V)
    (sim : A → X → D → V) (allowed : A → Prop)
    (tests : (V → Bool) → Prop) (epsilon : ℚ) : Prop :=
  ∀ a, allowed a → ∀ x w, valid x w →
    ComputationalDistanceBound tests (real a x w) (sim a x) epsilon

/-- The seeded source is NOT uniformly distributed over the ideal field-mask
space. No statistical closeness to an enormous uniform mask vector is claimed
for a concrete fixed hash. This hop needs a computational reduction, or a
separately specified bounded-query ideal random-oracle experiment. -/
def SeedExpansionHybridGoal
    (tests : (V → Bool) → Prop)
    (seeded : C → V) (ideal : D → V) (epsilonSeed : ℚ) : Prop :=
  ComputationalDistanceBound tests seeded ideal epsilonSeed

end
end AspisV8Privacy
