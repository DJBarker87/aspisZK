-- PCVZ_ generic lemma: Aeneas `loop` whose body result is projected through a function on the `done` payload.
-- Used where the gate (older Aeneas emission) returns only part of what the frozen emission returns from a loop.
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
open Lean.Order
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxRecDepth 2048
namespace PRVEq_P3W

/-- project the `done` payload of a control-flow value -/
def mapCF {α β γ : Type _} (f : β → γ) : ControlFlow α β → ControlFlow α γ
  | ControlFlow.cont a => ControlFlow.cont a
  | ControlFlow.done b => ControlFlow.done (f b)

/-- one step of the Aeneas `loop` functional -/
def bs {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) : Result β :=
  match body x with
  | ok r => match r with
    | ControlFlow.cont x' => h x'
    | ControlFlow.done y => ok y
  | fail e => fail e
  | div => div

theorem bs_mono {α β : Type _} (body : α → Result (ControlFlow α β)) (h1 h2 : α → Result β)
    (hle : ∀ x, h1 x ⊑ h2 x) (x : α) : bs body h1 x ⊑ bs body h2 x := by
  unfold bs
  cases body x with
  | ok r => cases r with
    | cont x' => exact hle x'
    | done y => exact PartialOrder.rel_refl
  | fail e => exact PartialOrder.rel_refl
  | div => exact PartialOrder.rel_refl

theorem loop_unfold {α β : Type _} (body : α → Result (ControlFlow α β)) (x : α) :
    loop body x = bs body (loop body) x := by
  rw [loop]; rfl

/-- projection of a result through `f` -/
def mapR {β γ : Type _} (f : β → γ) : Result β → Result γ
  | ok b => ok (f b)
  | fail e => fail e
  | div => div

theorem rel_of_eq' {γ : Type _} [Lean.Order.PartialOrder γ] {a b : γ} (h : a = b) : a ⊑ b := by
  rw [h]

theorem loop_le_aux {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hg : ∀ x, bs body g x ⊑ g x) : ∀ x, loop body x ⊑ g x := by
  refine loop.fixpoint_induct body (fun f => ∀ x, f x ⊑ g x) ?_ ?_
  · exact admissible_pi_apply (fun x (r : Result β) => r ⊑ g x)
      (fun x => admissible_flatOrder (b := (div : Result β)) (fun r : Result β => r ⊑ g x) FlatOrder.rel.bot)
  · intro f hf x
    exact PartialOrder.rel_trans (bs_mono body f g hf x) (hg x)

theorem loop_map {α β γ : Type _} (F : α → Result (ControlFlow α β)) (G : α → Result (ControlFlow α γ))
    (f : β → γ) (hrel : ∀ x, G x = (do let cf ← F x; ok (mapCF f cf))) :
    ∀ x, loop G x = mapR f (loop F x) := by
  -- key one-step identity: bs G (mapR f ∘ h) x = mapR f (bs F h x)
  have hstep : ∀ (h : α → Result β) (x : α), bs G (fun y => mapR f (h y)) x = mapR f (bs F h x) := by
    intro h x
    unfold bs
    rw [hrel x]
    cases hx : F x with
    | ok r => cases r with
      | cont x' => simp [mapCF, mapR]
      | done y => simp [mapCF, mapR]
    | fail e => simp [mapR]
    | div => simp [mapR]
  intro x
  apply PartialOrder.rel_antisymm
  · -- loop G ⊑ mapR f ∘ loop F
    have := PRVEq_P3W.loop_le_aux G (fun y => mapR f (loop F y)) (fun y => by
      apply rel_of_eq'
      rw [hstep (loop F) y, ← loop_unfold F y]) x
    exact this
  · -- mapR f ∘ loop F ⊑ loop G, by fixpoint induction on loop F
    refine (loop.fixpoint_induct F (fun h => ∀ y, mapR f (h y) ⊑ loop G y) ?_ ?_) x
    · exact admissible_pi_apply (fun y (r : Result β) => mapR f r ⊑ loop G y)
        (fun y => admissible_flatOrder (b := (div : Result β)) (fun r : Result β => mapR f r ⊑ loop G y)
          (FlatOrder.rel.bot : (div : Result γ) ⊑ loop G y))
    · intro h hh y
      change mapR f (bs F h y) ⊑ loop G y
      have h1 : mapR f (bs F h y) = bs G (fun z => mapR f (h z)) y := (hstep h y).symm
      rw [h1]
      refine PartialOrder.rel_trans (bs_mono G _ _ hh y) ?_
      apply rel_of_eq'
      rw [← loop_unfold G y]

end PRVEq_P3W

#print axioms PRVEq_P3W.loop_map
