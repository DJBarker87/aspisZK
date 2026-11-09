import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
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


theorem bs_bind {α β : Type _} (body : α → Result (ControlFlow α β)) (h : α → Result β) (x : α) :
    bs body h x = Bind.bind (body x) (fun r => match r with
      | ControlFlow.cont x' => h x'
      | ControlFlow.done y => ok y) := by
  unfold bs
  cases body x with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

theorem ite_bind {α β : Type _} (c : Prop) [Decidable c] (a b : Result α) (K : α → Result β) :
    Bind.bind (if c then a else b) K = if c then Bind.bind a K else Bind.bind b K := by
  by_cases hc : c <;> simp [hc]

theorem dite_bind {α β : Type _} (c : Prop) [Decidable c] (a : c → Result α) (b : ¬c → Result α)
    (K : α → Result β) :
    Bind.bind (dite c a b) K = dite c (fun h => Bind.bind (a h) K) (fun h => Bind.bind (b h) K) := by
  by_cases hc : c <;> simp [hc]


theorem bind_congr {α β : Type _} {m : Result α} {f f' : α → Result β} (h : ∀ a, f a = f' a) :
    Bind.bind m f = Bind.bind m f' := by
  have : f = f' := funext h
  rw [this]

theorem ite_congr' {α : Type _} (c : Prop) [Decidable c] {a a' b b' : Result α}
    (h1 : a = a') (h2 : b = b') : (if c then a else b) = (if c then a' else b') := by
  rw [h1, h2]

theorem dite_congr' {α : Type _} (c : Prop) [Decidable c] {a a' : c → Result α} {b b' : ¬c → Result α}
    (h1 : ∀ h, a h = a' h) (h2 : ∀ h, b h = b' h) : dite c a b = dite c a' b' := by
  have e1 : a = a' := funext h1
  have e2 : b = b' := funext h2
  rw [e1, e2]


theorem rel_of_eq' {γ : Type _} [Lean.Order.PartialOrder γ] {a b : γ} (h : a = b) : a ⊑ b := by
  rw [h]

theorem loop_eq_of_le {α β : Type _} (body : α → Result (ControlFlow α β)) (g : α → Result β)
    (hpre : ∀ x, bs body g x ⊑ g x) (hge : ∀ x, g x ⊑ loop body x) :
    ∀ x, loop body x = g x :=
  fun x => PartialOrder.rel_antisymm (loop_le body g hpre x) (hge x)
#print axioms loop_eq_of_le

theorem adm_le5 {α1 α2 α3 α4 α5 β : Type _} (h : α1 → α2 → α3 → α4 → α5 → Result β) :
    admissible (fun f : α1 → α2 → α3 → α4 → α5 → Result β => ∀ x1 x2 x3 x4 x5, f x1 x2 x3 x4 x5 ⊑ h x1 x2 x3 x4 x5) :=
  admissible_pi_apply (fun x1 (g : α2 → α3 → α4 → α5 → Result β) => ∀ x2 x3 x4 x5, g x2 x3 x4 x5 ⊑ h x1 x2 x3 x4 x5)
    (fun a => adm_le4 (h a))

theorem adm_le6 {α1 α2 α3 α4 α5 α6 β : Type _} (h : α1 → α2 → α3 → α4 → α5 → α6 → Result β) :
    admissible (fun f : α1 → α2 → α3 → α4 → α5 → α6 → Result β => ∀ x1 x2 x3 x4 x5 x6, f x1 x2 x3 x4 x5 x6 ⊑ h x1 x2 x3 x4 x5 x6) :=
  admissible_pi_apply (fun x1 (g : α2 → α3 → α4 → α5 → α6 → Result β) => ∀ x2 x3 x4 x5 x6, g x2 x3 x4 x5 x6 ⊑ h x1 x2 x3 x4 x5 x6)
    (fun a => adm_le5 (h a))

theorem uncurry_proj {α β γ : Type _} (f : α → β → γ) (p : α × β) :
    Aeneas.Std.uncurry f p = f p.1 p.2 := by cases p; rfl

/-- normalise both sides, one side at a time (a whole-goal `simp` can refuse on dependent numerals) -/
macro "prv_norm" : tactic => `(tactic| (
  try (conv_lhs => simp only [bind_assoc_eq, ite_bind, dite_bind, bind_tc_ok, Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair, uncurry_proj])
  try (conv_rhs => simp only [bind_assoc_eq, ite_bind, dite_bind, bind_tc_ok, Aeneas.Std.bind_ok, Aeneas.Std.uncurry_apply_pair, uncurry_proj])))

/-- push the loop continuation inward and match the two do-block shapes -/
macro "prv_peel" : tactic => `(tactic| (
  prv_norm
  repeat (first
    | with_reducible rfl
    | (apply PRVC.bind_congr; intro a; try (obtain ⟨_, _⟩ := a); prv_norm)
    | (apply PRVC.ite_congr'; prv_norm)
    | (apply PRVC.dite_congr' <;> intro h)
    | (split <;> prv_norm))))

end PRVC
