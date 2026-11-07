import NNG_EmittedPureCall
set_option autoImplicit false
namespace AspisR1.NNG_EnvCallGraph136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_ObservationAlgebra
open NNG_EmittedCallGraph

/-- Pointwise graph equality at the actual Env. A source call dictionary may
capture this Env's reservation and oracle replies, rather than freezing them
for all other environments. No VLib operation is instantiated here. -/
theorem effect_at {Args A B C : Type} (field : RSL.Child C B) (arg : C)
    (hd : field.dom arg) (decode : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) (env : RSL.Env) (model : RSL.Obs B)
    (source : (⟨exit decode r, events env (.call site args r)⟩ : RSL.Obs B) = model)
    (fieldGraph : ∀ o, field.law arg env o ↔ o = model) :
    RSL.Spec.map decode (NNG_Interpret136.call events site args r) env = field.run arg env := by
  rw [call_projection]
  funext out
  apply propext
  change (out = ⟨exit decode r, events env (.call site args r)⟩) ↔
    field.dom arg ∧ field.law arg env out
  rw [source]
  exact ⟨fun h => ⟨hd, (fieldGraph out).mpr h⟩,
    fun h => (fieldGraph out).mp h.2⟩
#print axioms effect_at

theorem pure_at {Args A B : Type} (decode : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) (env : RSL.Env) (model field : B)
    (source : resultMap decode r = .ok model) (fieldGraph : field = model)
    (silent : events env (.call site args r) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events site args r) env = (RSL.Spec.pure field) env := by
  rw [call_projection]
  funext out
  change (out = ⟨exit decode r, events env (.call site args r)⟩) = (out = ⟨.ret field, []⟩)
  rw [NNG_EmittedPureCall.returned_exit decode r model source, silent, fieldGraph]
#print axioms pure_at
end AspisR1.NNG_EnvCallGraph136
