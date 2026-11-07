import NNG_Interpret136
set_option autoImplicit false
namespace AspisR1.NNG_InterpretProjection
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_ObservationAlgebra NNG_Interpret136

def mapExit {A B : Type} (f : A → B) : RSL.Exit A → RSL.Exit B
  | .ret a => .ret (f a)
  | .abort => .abort
  | .diverge => .diverge

def mapObs {A B : Type} (f : A → B) (o : RSL.Obs A) : RSL.Obs B :=
  ⟨mapExit f o.exit, o.events⟩

theorem map_graph {A B : Type} (f : A → B) (head : RSL.Env → RSL.Obs A) :
    RSL.Spec.map f (graph head) = graph (fun env => mapObs f (head env)) := by
  change RSL.Spec.bind (graph head)
    (fun a => graph (fun _ => ⟨.ret (f a), []⟩)) = _
  rw [graph_bind]
  apply congrArg graph
  funext env
  generalize head env = o
  rcases o with ⟨x,e⟩
  cases x with
  | ret a => simp only [append, mapObs, mapExit, List.append_nil]
  | abort => rfl
  | diverge => rfl
#print axioms map_graph

theorem map_observation {A B : Type} (f : A → B)
    (events : NMT_CallTree.Event → List RSL.Event) (code : Code A) :
    mapObs f (observation id events code) = observation f events code := by
  unfold observation
  generalize run code = out
  rcases out with ⟨r,log⟩
  cases r <;> rfl
#print axioms map_observation

/-- Carrier projection preserves all observation arms and the exact prefix. -/
theorem projected_graph {A B : Type} (f : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event) (code : Code A) :
    RSL.Spec.map f (interpret events code) =
      graph (fun env => observation f (events env) code) := by
  rw [exact_graph, map_graph]
  apply congrArg graph
  funext env
  exact map_observation f (events env) code
#print axioms projected_graph

/-- The relational fold consumes THIS actual emitted observation, rather
than an independently supplied child result, log, endpoint or successful run. -/
theorem actual_emitted {H W : Type} (VL : RSL.VLib) (c : NNG_Emitted.Calls)
    (input : RSL.TX1_136.Args VL → RSL.Observer → RSL.Env → NNG_Emitted.Parent H W)
    (decode : NNG_Emitted.Output H → Except VL.WErr (RSL.Verified VL))
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (a : RSL.TX1_136.Args VL) (obs : RSL.Observer) (env : RSL.Env) :
    RSL.Spec.map decode (interpret events (NNG_FinishTree.tree c (input a obs env)))
      env (producer VL c input decode events a obs env) := by
  rw [projected_graph, producer_tree]
  rfl
#print axioms actual_emitted
end AspisR1.NNG_InterpretProjection
