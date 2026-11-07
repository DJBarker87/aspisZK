import NNG_Observed136
set_option autoImplicit false
namespace AspisR1.NNG_ObservationAlgebra
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136

/-- Deterministic chronological composition; only returning paths enter k. -/
def append {A B : Type} (o : RSL.Obs A) (k : A → RSL.Obs B) : RSL.Obs B :=
  match o.exit with
  | .ret a => let tail := k a; ⟨tail.exit, o.events ++ tail.events⟩
  | .abort => ⟨.abort, o.events⟩
  | .diverge => ⟨.diverge, o.events⟩

def graph {A : Type} (o : RSL.Env → RSL.Obs A) : RSL.Spec A :=
  fun env out => out = o env

/-- The result of a bind, paired with its exact typed call prefix. -/
theorem run_bind {A B : Type} (code : Code A) (k : A → Code B) :
    run (NMT_CallTree.bind code k) =
      match (run code).1 with
      | .ok a => let tail := run (k a); (tail.1, (run code).2 ++ tail.2)
      | .fail e => (.fail e, (run code).2)
      | .div => (.div, (run code).2) := by
  induction code with
  | done a => rfl
  | plain r next ih =>
    cases r with
    | ok a => exact ih a
    | fail e => rfl
    | div => rfl
  | call site arg r next ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok a =>
      simp only [NMT_CallTree.bind, run, ih]
      generalize run (next a) = out
      rcases out with ⟨result,log⟩
      cases result <;> rfl
#print axioms run_bind

/-- Ordered event interpretation commutes with chronological bind, including
non-returning heads; no suffix is appended to a stopped head. -/
theorem observation_bind {A B C : Type} (decode : B → C)
    (events : NMT_CallTree.Event → List RSL.Event) (code : Code A) (k : A → Code B) :
    observation decode events (NMT_CallTree.bind code k) =
      append (observation id events code) (fun a => observation decode events (k a)) := by
  unfold observation
  rw [run_bind]
  generalize run code = out
  rcases out with ⟨result,log⟩
  cases result with
  | ok a => simp only [exit, append, List.flatMap_append]
  | fail e => rfl
  | div => rfl
#print axioms observation_bind

/-- Complete singleton graphs compose with the SAME head and suffix logs. -/
theorem graph_bind {A B : Type} (head : RSL.Env → RSL.Obs A)
    (tail : A → RSL.Env → RSL.Obs B) :
    RSL.Spec.bind (graph head) (fun a => graph (tail a)) =
      graph (fun env => append (head env) (fun a => tail a env)) := by
  funext env out
  apply propext
  constructor
  · intro h
    rcases h with ⟨a,e,o2,hm,hk,ho⟩ | ⟨e,hm,ho⟩ | ⟨e,hm,ho⟩
    · change RSL.Obs.mk (.ret a) e = head env at hm
      change o2 = tail a env at hk
      change out = append (head env) (fun a => tail a env)
      rw [←hm]
      change out = ⟨(tail a env).exit, e ++ (tail a env).events⟩
      rw [←hk]
      exact ho
    · change RSL.Obs.mk .abort e = head env at hm
      change out = append (head env) (fun a => tail a env)
      rw [←hm]
      exact ho
    · change RSL.Obs.mk .diverge e = head env at hm
      change out = append (head env) (fun a => tail a env)
      rw [←hm]
      exact ho
  · intro h
    change out = append (head env) (fun a => tail a env) at h
    generalize he : head env = o at h
    rcases o with ⟨x,e⟩
    cases x with
    | ret a => exact Or.inl ⟨a,e,tail a env,he.symm,rfl,h⟩
    | abort => exact Or.inr (Or.inl ⟨e,he.symm,h⟩)
    | diverge => exact Or.inr (Or.inr ⟨e,he.symm,h⟩)
#print axioms graph_bind
end AspisR1.NNG_ObservationAlgebra
