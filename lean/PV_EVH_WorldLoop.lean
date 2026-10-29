import PV_EVH_World
set_option autoImplicit false
namespace PV_EVH_WorldLoop
open Aeneas Aeneas.Std PV_EVH_World

/-- Exhaustion is an interpreter boundary, not a source .div result. -/
inductive Status (A : Type) where
  | finished (result : Result A)
  | exhausted

structure Prefix (A : Type) where
  status : Status A
  world : World
  events : List PV_RJ4IDB.NativeEvent

variable {S A : Type}

def loop (body : S → M (ControlFlow S A)) : Nat → S → World → Prefix A
  | 0,_,w => ⟨.exhausted,w,[]⟩
  | n+1,s,w =>
    let r := body s w
    match r.result with
    | .fail e => ⟨.finished (.fail e),r.world,r.events⟩
    | .div => ⟨.finished .div,r.world,r.events⟩
    | .ok (.done a) => ⟨.finished (.ok a),r.world,r.events⟩
    | .ok (.cont s') =>
      let t := loop body n s' r.world
      ⟨t.status,t.world,r.events ++ t.events⟩

theorem zero_exhausted (body : S → M (ControlFlow S A)) (s : S) (w : World) :
    (loop body 0 s w).status = .exhausted := rfl

theorem exhausted_prefix (body : S → M (ControlFlow S A))
    (n : Nat) (s next : S) (w : World)
    (h : (body s w).result = .ok (.cont next)) :
    (loop body (n+1) s w).events =
      (body s w).events ++ (loop body n next (body s w).world).events := by
  simp only [loop,h]

/-- Non-regression is restricted to completed finite evaluations whose
primitive answers agree with one dictionary. No claim is made at exhaustion. -/
theorem fixed_finished (body : S → M (ControlFlow S A))
    (source : S → Result (ControlFlow S A))
    (compatible : ∀ s, FixedView (body s) (source s))
    (n : Nat) (s : S) (w : World) (r : Result A)
    (finished : (loop body n s w).status = .finished r) :
    Aeneas.Std.loop source s = r := by
  induction n generalizing s w r with
  | zero => cases finished
  | succ n ih =>
    cases hs : source s with
    | fail e =>
      have he := compatible s w
      rw [hs] at he
      simp only [loop,he] at finished
      cases finished
      rw [Aeneas.Std.loop.eq_def,hs]
    | div =>
      have he := compatible s w
      rw [hs] at he
      simp only [loop,he] at finished
      cases finished
      rw [Aeneas.Std.loop.eq_def,hs]
    | ok cf =>
      cases cf with
      | done a =>
        have he := compatible s w
        rw [hs] at he
        simp only [loop,he] at finished
        cases finished
        rw [Aeneas.Std.loop.eq_def,hs]
      | cont next =>
        have he := compatible s w
        rw [hs] at he
        simp only [loop,he] at finished
        rw [Aeneas.Std.loop.eq_def,hs]
        exact ih next (body s w).world r finished

#print axioms zero_exhausted
#print axioms exhausted_prefix
#print axioms fixed_finished
end PV_EVH_WorldLoop
