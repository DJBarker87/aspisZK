import AspisV8R19.SamplerObservation

set_option autoImplicit false
namespace AspisV8R19.SamplerObservedLaws
open Aeneas Aeneas.Std Result ControlFlow SamplerObservation
variable {A B S : Type}

theorem bind_apply (m : Observed A) (f : A → Observed B) (history : Trace) :
    (m >>= f) history = (do let (a,t) ← m history; f a t) := rfl
theorem pure_apply (a : A) (history : Trace) :
    (pure a : Observed A) history=.ok (a,history) := rfl
theorem lift_apply (r : Result A) (history : Trace) :
    (liftM r : Observed A) history=(do let a ← r; .ok (a,history)) := rfl
theorem map_apply (f : A → B) (m : Observed A) (history : Trace) :
    (f <$> m) history=(do let (a,t) ← m history; .ok (f a,t)) := rfl

theorem loop_unfold (body : S → Observed (ControlFlow S A)) (s : S) (history : Trace) :
    observedLoop body s history = (do
      let (r,t) ← body s history
      match r with
      | .cont s1 => observedLoop body s1 t
      | .done a => .ok (a,t)) := by
  rw [observedLoop,loop.eq_def]
  cases h : body s history with
  | fail e => simp only [h,bind_tc_fail]
  | div => simp only [h,bind_tc_div]
  | ok pair =>
      rcases pair with ⟨r,t⟩
      cases r <;> simp only [h,bind_tc_ok,observedLoop]

#print axioms bind_apply
#print axioms pure_apply
#print axioms lift_apply
#print axioms map_apply
#print axioms loop_unfold
end AspisV8R19.SamplerObservedLaws
