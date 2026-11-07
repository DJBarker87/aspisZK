import NNG_InterpretProjection
set_option autoImplicit false
namespace AspisR1.NNG_EmittedCallGraph
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_ObservationAlgebra NNG_Interpret136 NNG_InterpretProjection

def resultMap {A B : Type} (f : A → B) : Result A → Result B
  | .ok a => .ok (f a)
  | .fail e => .fail e
  | .div => .div

theorem call_projection {Args A B : Type} (decode : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) :
    RSL.Spec.map decode (NNG_Interpret136.call events site args r) =
      graph (fun env => ⟨exit decode r, events env (.call site args r)⟩) := by
  rw [NNG_Interpret136.call, map_graph]
  apply congrArg graph
  funext env
  cases r <;> rfl
#print axioms call_projection

/-- A SAME actual emitted call equals the corresponding VLib Child.run,
when its complete observation equals the CLOSED deterministic model and the
field law is that model's graph. The entered call's own domain is explicit. -/
theorem closed_at {Args A B C : Type} (field : RSL.Child C B) (arg : C)
    (hd : field.dom arg) (decode : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) (model : RSL.Env → RSL.Obs B)
    (source : ∀ env, (⟨exit decode r, events env (.call site args r)⟩ : RSL.Obs B) = model env)
    (fieldGraph : ∀ env o, field.law arg env o ↔ o = model env) :
    RSL.Spec.map decode (NNG_Interpret136.call events site args r) = field.run arg := by
  rw [call_projection]
  funext env out
  apply propext
  change (out = ⟨exit decode r, events env (.call site args r)⟩) ↔
    field.dom arg ∧ field.law arg env out
  rw [source env]
  exact ⟨fun h => ⟨hd, (fieldGraph env out).mpr h⟩,
    fun h => (fieldGraph env out).mp h.2⟩
#print axioms closed_at
end AspisR1.NNG_EmittedCallGraph
