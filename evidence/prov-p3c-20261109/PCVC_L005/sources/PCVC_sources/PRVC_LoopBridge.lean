import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 400000
open Lean.Order

namespace PRVC

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
#print axioms loop_unfold


theorem adm_le {β : Type _} (g : Result β) : admissible (fun r : Result β => r ⊑ g) :=
  admissible_flatOrder (b := (div : Result β)) (fun r : Result β => r ⊑ g) FlatOrder.rel.bot

theorem loop_le {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hg : ∀ x, bs body g x ⊑ g x) : ∀ x, loop body x ⊑ g x := by
  refine loop.fixpoint_induct body (fun f => ∀ x, f x ⊑ g x) ?_ ?_
  · exact admissible_pi_apply (fun x (r : Result β) => r ⊑ g x) (fun x => adm_le (g x))
  · intro f hf x
    exact PartialOrder.rel_trans (bs_mono body f g hf x) (hg x)

theorem loop_eq {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hfix : ∀ x, g x = bs body g x)
    (hmin : ∀ h : α → Result β, (∀ x, bs body h x ⊑ h x) → ∀ x, g x ⊑ h x) :
    ∀ x, loop body x = g x := by
  intro x
  have h1 : loop body x ⊑ g x := loop_le body g (fun y => by rw [← hfix y]) x
  have h2 : g x ⊑ loop body x :=
    hmin (loop body) (fun y => by rw [← loop_unfold]) x
  exact PartialOrder.rel_antisymm h1 h2
#print axioms loop_eq


/-- curried-pair admissibility helpers for `X.fixpoint_induct` motives -/
theorem adm_le1 {α β : Type _} (h : α → Result β) :
    admissible (fun f : α → Result β => ∀ a, f a ⊑ h a) :=
  admissible_pi_apply (fun a (r : Result β) => r ⊑ h a) (fun a => adm_le (h a))

theorem adm_le2 {α₁ α₂ β : Type _} (h : α₁ → α₂ → Result β) :
    admissible (fun f : α₁ → α₂ → Result β => ∀ a b, f a b ⊑ h a b) :=
  admissible_pi_apply (fun a (g : α₂ → Result β) => ∀ b, g b ⊑ h a b)
    (fun a => adm_le1 (h a))

theorem adm_le3 {α₁ α₂ α₃ β : Type _} (h : α₁ → α₂ → α₃ → Result β) :
    admissible (fun f : α₁ → α₂ → α₃ → Result β => ∀ a b c, f a b c ⊑ h a b c) :=
  admissible_pi_apply (fun a (g : α₂ → α₃ → Result β) => ∀ b c, g b c ⊑ h a b c)
    (fun a => adm_le2 (h a))

theorem adm_le4 {α₁ α₂ α₃ α₄ β : Type _} (h : α₁ → α₂ → α₃ → α₄ → Result β) :
    admissible (fun f : α₁ → α₂ → α₃ → α₄ → Result β => ∀ a b c d, f a b c d ⊑ h a b c d) :=
  admissible_pi_apply (fun a (g : α₂ → α₃ → α₄ → Result β) => ∀ b c d, g b c d ⊑ h a b c d)
    (fun a => adm_le3 (h a))

end PRVC
