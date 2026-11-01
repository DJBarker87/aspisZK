import PV_EVH_WorldLoop
set_option autoImplicit false
namespace PV_EVH_Prefix
open Aeneas Aeneas.Std PV_EVH_World PV_EVH_WorldLoop

/-- Finite execution, with exhaustion separate from a source Result. -/
abbrev P (A : Type) := World → Prefix A

def ofM {A : Type} (m : M A) : P A := fun w =>
  let r := m w
  ⟨.finished r.result,r.world,r.events⟩

def lift {A : Type} (r : Result A) : P A := ofM (PV_EVH_World.lift r)

def bind {A B : Type} (m : P A) (k : A → P B) : P B := fun w =>
  let r := m w
  match r.status with
  | .exhausted => ⟨.exhausted,r.world,r.events⟩
  | .finished (.fail e) => ⟨.finished (.fail e),r.world,r.events⟩
  | .finished .div => ⟨.finished .div,r.world,r.events⟩
  | .finished (.ok a) =>
    let s := k a r.world
    ⟨s.status,s.world,r.events ++ s.events⟩

instance : Monad P where
  pure a := lift (.ok a)
  bind := bind

/-- Compatibility only asserts erasure when the finite execution finishes. -/
def FinishedView {A : Type} (m : P A) (source : Result A) : Prop :=
  ∀ w r, (m w).status = .finished r → source = r

theorem ofM_fixed {A : Type} (m : M A) (r : Result A)
    (h : FixedView m r) : FinishedView (ofM m) r := by
  intro w s hs
  have he : (m w).result = s := Status.finished.inj hs
  exact (h w).symm.trans he

theorem lift_fixed {A : Type} (r : Result A) : FinishedView (lift r) r :=
  ofM_fixed _ _ (fixed_lift r)

theorem bind_exhausted {A B : Type} (m : P A) (k : A → P B)
    (w : World) (h : (m w).status = .exhausted) :
    bind m k w = ⟨.exhausted,(m w).world,(m w).events⟩ := by
  simp only [bind,h]

theorem bind_ok {A B : Type} (m : P A) (k : A → P B)
    (w : World) (a : A) (h : (m w).status = .finished (.ok a)) :
    bind m k w = ⟨(k a (m w).world).status,(k a (m w).world).world,
      (m w).events ++ (k a (m w).world).events⟩ := by
  simp only [bind,h]

theorem bind_assoc {A B C : Type} (m : P A) (k : A → P B) (f : B → P C) :
    bind (bind m k) f = bind m (fun a => bind (k a) f) := by
  funext w
  cases hm : (m w).status with
  | exhausted => simp only [bind,hm]
  | finished r =>
    cases r with
    | fail e => simp only [bind,hm]
    | div => simp only [bind,hm]
    | ok a =>
      cases hk : (k a (m w).world).status with
      | exhausted => simp only [bind,hm,hk]
      | finished s => cases s <;> simp only [bind,hm,hk,List.append_assoc]

theorem bind_fixed {A B : Type} (m : P A) (k : A → P B)
    (r : Result A) (f : A → Result B) (hm : FinishedView m r)
    (hk : ∀ a, FinishedView (k a) (f a)) :
    FinishedView (bind m k) (Aeneas.Std.bind r f) := by
  intro w s hs
  cases he : (m w).status with
  | exhausted => simp only [bind,he] at hs; cases hs
  | finished t =>
    have hr := hm w t he
    rw [hr]
    cases t with
    | fail e => simp only [bind,he] at hs; cases hs; rfl
    | div => simp only [bind,he] at hs; cases hs; rfl
    | ok a =>
      simp only [bind,he] at hs
      exact hk a (m w).world s hs

#print axioms ofM_fixed
#print axioms lift_fixed
#print axioms bind_exhausted
#print axioms bind_ok
#print axioms bind_assoc
#print axioms bind_fixed
end PV_EVH_Prefix
