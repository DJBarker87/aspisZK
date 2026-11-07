import NMS_Effect242
import NMS_RSLRefine
set_option autoImplicit false
namespace NMS_Interpreted
open Aeneas Aeneas.Std
/-- The retained std/extraction interpretation of outer Result. Stop arms
carry no successful value or post-state, and no additional event is invented. -/
def liftResult {A : Type} : Result A → RSL.Spec A
 | .ok value => RSL.Spec.pure value
 | .fail _ => RSL.Spec.panic
 | .div => fun _ observation => observation = ⟨.diverge,[]⟩

instance : MonadLift Result RSL.Spec where
 monadLift := liftResult

def mapExit {A B : Type} (value : A → B) : RSL.Exit A → RSL.Exit B
 | .ret a => .ret (value a)
 | .abort => .abort
 | .diverge => .diverge

def mapObs {A B : Type} (value : A → B) (observation : RSL.Obs A) : RSL.Obs B :=
 ⟨mapExit value observation.exit,observation.events⟩

def Simulates {A B : Type} (value : A → B) (actual : RSL.Spec A) (model : RSL.Spec B) : Prop :=
 ∀ env observation, actual env observation → model env (mapObs value observation)

theorem pure {A B : Type} (value : A → B) (a : A) :
 Simulates value (RSL.Spec.pure a) (RSL.Spec.pure (value a)) := by
 intro env observation run
 subst observation
 rfl

theorem bind {A B C D : Type} (value : A → C) (output : B → D)
 (actual : RSL.Spec A) (model : RSL.Spec C)
 (next : A → RSL.Spec B) (later : C → RSL.Spec D)
 (first : Simulates value actual model)
 (rest : ∀ a, Simulates output (next a) (later (value a))) :
 Simulates output (RSL.Spec.bind actual next) (RSL.Spec.bind model later) := by
 intro env observation run
 rcases run with ⟨a,evs,o2,hm,hk,ho⟩ | ⟨evs,hm,ho⟩ | ⟨evs,hm,ho⟩
 · subst observation
   exact Or.inl ⟨value a,evs,mapObs output o2,first env _ hm,rest a env o2 hk,rfl⟩
 · subst observation
   exact Or.inr (Or.inl ⟨evs,first env _ hm,rfl⟩)
 · subst observation
   exact Or.inr (Or.inr ⟨evs,first env _ hm,rfl⟩)

theorem lift_ok {A : Type} (a : A) : liftResult (.ok a) = RSL.Spec.pure a := rfl
theorem lift_fail {A : Type} (error : Error) :
 (liftResult (.fail error) : RSL.Spec A) = RSL.Spec.panic := rfl
theorem lift_div {A : Type} (env : RSL.Env) (observation : RSL.Obs A) :
 liftResult .div env observation ↔ observation = ⟨.diverge,[]⟩ := Iff.rfl

theorem map_ret {A B : Type} (value : A → B) (a : A) (events : List RSL.Event) :
 mapObs value ⟨.ret a,events⟩ = ⟨.ret (value a),events⟩ := rfl
theorem map_abort {A B : Type} (value : A → B) (events : List RSL.Event) :
 mapObs value (⟨.abort,events⟩ : RSL.Obs A) = ⟨.abort,events⟩ := rfl
#print axioms pure
#print axioms bind
#print axioms lift_ok
#print axioms lift_fail
#print axioms lift_div
#print axioms map_ret
#print axioms map_abort
end NMS_Interpreted
