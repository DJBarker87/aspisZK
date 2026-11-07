import NNG_ObservationAlgebra
set_option autoImplicit false
namespace AspisR1.NNG_Interpret136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_ObservationAlgebra

/-- Standard computation: an outer failure or divergence stops here, silently. -/
def silent {A : Type} (r : Result A) : RSL.Spec A :=
  graph (fun _ => ⟨exit id r, []⟩)

/-- A typed source call carries its CLOSED-model event prefix on EVERY arm. -/
def call {Args A : Type} (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) : RSL.Spec A :=
  graph (fun env => ⟨exit id r, events env (.call site args r)⟩)

/-- Relational interpretation of the actual reified body. There is no native
post-state argument and no independently chosen result or call log. -/
def interpret {A : Type} (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) :
    Code A → RSL.Spec A
  | .done a => RSL.Spec.pure a
  | .plain r k => RSL.Spec.bind (silent r) (fun a => interpret events (k a))
  | .call s args r k => RSL.Spec.bind (call events s args r) (fun a => interpret events (k a))

theorem silent_graph {A : Type} (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (r : Result A) :
    silent r = graph (fun env => observation id (events env) (.plain r .done)) := by
  cases r <;> rfl
#print axioms silent_graph

theorem call_graph {Args A : Type} (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) :
    call events site args r =
      graph (fun env => observation id (events env) (invoke site args r)) := by
  cases r <;> simp only [call, graph, observation, invoke, run, exit, id_eq,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
#print axioms call_graph

/-- Structural induction over source code, with all replies universally
quantified. This identifies the complete relation, including stopped prefixes. -/
theorem exact_graph {A : Type} (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (code : Code A) :
    interpret events code = graph (fun env => observation id (events env) code) := by
  induction code with
  | done a => rfl
  | plain r k ih =>
    change RSL.Spec.bind (silent r) (fun a => interpret events (k a)) = _
    have tails : (fun a => interpret events (k a)) =
        (fun a => graph (fun env => observation id (events env) (k a))) := funext ih
    rw [tails, silent_graph events, graph_bind]
    funext env out
    unfold graph
    rw [←observation_bind]
    rfl
  | call s args r k ih =>
    change RSL.Spec.bind (call events s args r) (fun a => interpret events (k a)) = _
    have tails : (fun a => interpret events (k a)) =
        (fun a => graph (fun env => observation id (events env) (k a))) := funext ih
    rw [tails, call_graph, graph_bind]
    funext env out
    unfold graph
    rw [←observation_bind]
    rfl
#print axioms exact_graph

/-- Interpretation is constructive at the actual observation: no existence
or successful-return hypothesis is required from the caller. -/
theorem actual {A : Type} (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (code : Code A) (env : RSL.Env) :
    interpret events code env (observation id (events env) code) := by
  rw [exact_graph]
  rfl
#print axioms actual
end AspisR1.NNG_Interpret136
