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
  have h1 : loop body x ⊑ g x := loop_le body g (fun y => by rw [← hfix y]; exact PartialOrder.rel_refl) x
  have h2 : g x ⊑ loop body x :=
    hmin (loop body) (fun y => by rw [← loop_unfold]; exact PartialOrder.rel_refl) x
  exact PartialOrder.rel_antisymm h1 h2
#print axioms loop_eq

def toy (n acc : Nat) : Result Nat :=
  if n = 0 then ok acc else toy (n-1) (acc+n)
partial_fixpoint

def toyBody : Nat × Nat → Result (ControlFlow (Nat × Nat) Nat) := fun (p : Nat × Nat) =>
  if p.1 = 0 then ok (done p.2) else ok (cont (p.1 - 1, p.2 + p.1))

theorem toy_eq : ∀ n acc, loop toyBody (n, acc) = toy n acc := by
  intro n acc
  refine loop_eq toyBody (fun p => toy p.1 p.2) ?_ ?_ (n, acc)
  · intro p
    show toy p.1 p.2 = _
    rw [toy]
    unfold bs toyBody
    by_cases h : p.1 = 0 <;> simp [h]
  · intro h hh p
    show toy p.1 p.2 ⊑ h p
    revert p
    refine toy.fixpoint_induct (fun f => ∀ p : Nat × Nat, f p.1 p.2 ⊑ h p) ?_ ?_
    · exact admissible_pi_apply (fun (p : Nat × Nat) (r : Result Nat) => r ⊑ h p) (fun p => adm_le (h p))
    · intro f hf p
      refine PartialOrder.rel_trans ?_ (hh p)
      unfold bs toyBody
      by_cases hp : p.1 = 0
      · simp [hp]; exact PartialOrder.rel_refl
      · simp [hp]; exact hf _
#print axioms toy_eq

end PRVC
