import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs

/-!
IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM.
Finite, nonempty, uniformly sampled coin spaces. This is a counting layer,
not a model of SHA-derived coins or a completed V8 simulator.
-/
set_option autoImplicit false
namespace AspisV8Privacy
noncomputable section
universe u v w

variable {C : Type u} {D : Type v} {V : Type w}

/-- The observable fiber, not an assumed output distribution. -/
def fiberCount [Fintype C] (f : C → V) (y : V) : Nat := by
  classical
  exact Fintype.card {c : C // f c = y}

def uniformProbability [Fintype C] [Nonempty C] (f : C → V) (y : V) : ℚ :=
  (fiberCount f y : ℚ) / (Fintype.card C : ℚ)

def SameUniformLaw [Fintype C] [Fintype D] [Nonempty C] [Nonempty D]
    (f : C → V) (g : D → V) : Prop :=
  ∀ y, uniformProbability f y = uniformProbability g y

/-- A concrete bijection of source coins transports observable fibers. -/
def observationFiberEquiv (f : C → V) (g : D → V) (e : C ≃ D)
    (commutes : ∀ c, g (e c) = f c) (y : V) :
    {c : C // f c = y} ≃ {d : D // g d = y} where
  toFun c := ⟨e c.val, (commutes c.val).trans c.property⟩
  invFun d := ⟨e.symm d.val, by
    rw [← commutes (e.symm d.val), e.apply_symm_apply]
    exact d.property⟩
  left_inv c := by apply Subtype.ext; exact e.symm_apply_apply c.val
  right_inv d := by apply Subtype.ext; exact e.apply_symm_apply d.val

theorem fiberCount_reindex [Fintype C] [Fintype D]
    (f : C → V) (g : D → V) (e : C ≃ D)
    (commutes : ∀ c, g (e c) = f c) (y : V) :
    fiberCount f y = fiberCount g y := by
  classical
  exact Fintype.card_congr (observationFiberEquiv f g e commutes y)

theorem sameUniformLaw_of_coinEquiv [Fintype C] [Fintype D]
    [Nonempty C] [Nonempty D] (f : C → V) (g : D → V) (e : C ≃ D)
    (commutes : ∀ c, g (e c) = f c) : SameUniformLaw f g := by
  intro y
  unfold uniformProbability
  rw [fiberCount_reindex f g e commutes y, Fintype.card_congr e]

/-- The same bijection also protects ANY deterministic public observation.
This is postprocessing, not protection against additional secret inputs. -/
theorem coinEquiv_postprocess [Fintype C] [Fintype D]
    [Nonempty C] [Nonempty D] {W : Type*}
    (f : C → V) (g : D → V) (e : C ≃ D)
    (commutes : ∀ c, g (e c) = f c) (observe : V → W) :
    SameUniformLaw (observe ∘ f) (observe ∘ g) := by
  apply sameUniformLaw_of_coinEquiv _ _ e
  intro c
  exact congrArg observe (commutes c)

#print axioms fiberCount_reindex
#print axioms sameUniformLaw_of_coinEquiv
#print axioms coinEquiv_postprocess
end
end AspisV8Privacy
