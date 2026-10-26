import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FiniteGraph

/-- An explicit buildStated world with a retained completion coordinate. This
is finite even when native states themselves form an infinite type. -/
structure World {Coins State : Type} (buildState : Coins → State) where
  coins : Coins
  state : State
  state_eq : state = buildState coins

def create {Coins State : Type} (buildState : Coins → State) (c : Coins) : World buildState :=
  ⟨c,buildState c,rfl⟩

def coordinates {Coins State : Type} (buildState : Coins → State) : World buildState ≃ Coins where
  toFun := World.coins
  invFun := create buildState
  left_inv := by
    rintro ⟨c,s,h⟩
    subst s
    rfl
  right_inv := fun _ => rfl

instance finite {Coins State : Type} (buildState : Coins → State) [Fintype Coins] :
    Fintype (World buildState) := Fintype.ofEquiv Coins (coordinates buildState).symm

instance nonempty {Coins State : Type} (buildState : Coins → State) [Nonempty Coins] :
    Nonempty (World buildState) := ⟨create buildState (Classical.choice inferInstance)⟩

theorem cardinality {Coins State : Type} (buildState : Coins → State) [Fintype Coins] :
    Fintype.card (World buildState) = Fintype.card Coins := Fintype.card_congr (coordinates buildState)

theorem sum_coordinates {Coins State : Type} (buildState : Coins → State) [Fintype Coins]
    (f : Coins → ℚ) : (∑ w : World buildState, f w.coins) = ∑ c : Coins, f c := by
  exact Fintype.sum_equiv (coordinates buildState) _ _ (fun _ => rfl)

theorem mean_coordinates {Coins State : Type} (buildState : Coins → State) [Fintype Coins]
    (f : Coins → ℚ) :
    (∑ w : World buildState, f w.coins) / Fintype.card (World buildState) =
      (∑ c : Coins, f c) / Fintype.card Coins := by
  rw [cardinality,sum_coordinates]

#print axioms create
#print axioms coordinates
#print axioms finite
#print axioms nonempty
#print axioms cardinality
#print axioms sum_coordinates
#print axioms mean_coordinates
end R1Z.PV_RunJoin_FiniteGraph
