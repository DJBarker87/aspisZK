import NNG_EmittedCallGraph
set_option autoImplicit false
namespace AspisR1.NNG_EmittedPureCall
open Aeneas Aeneas.Std Result NMT_CallTree NNG_Observed136 NNG_ObservationAlgebra NNG_Interpret136 NNG_EmittedCallGraph

theorem returned_exit {A B : Type} (decode : A → B) (r : Result A) (model : B)
    (source : resultMap decode r = .ok model) : exit decode r = .ret model := by
  cases r with
  | ok a => exact congrArg RSL.Exit.ret (Result.ok.inj source)
  | fail e => cases source
  | div => cases source
#print axioms returned_exit

/-- Pure source helper, including an inner Rust Err when B is Except. Only
an actual outer return and the CLOSED source's absence of effects are used. -/
theorem closed_at {Args A B : Type} (decode : A → B)
    (events : RSL.Env → NMT_CallTree.Event → List RSL.Event)
    (site : String) (args : Args) (r : Result A) (model field : B)
    (source : resultMap decode r = .ok model) (fieldGraph : field = model)
    (silent : ∀ env, events env (.call site args r) = []) :
    RSL.Spec.map decode (NNG_Interpret136.call events site args r) = RSL.Spec.pure field := by
  rw [call_projection]
  have same : (fun env => (⟨exit decode r, events env (.call site args r)⟩ : RSL.Obs B)) =
      (fun _ => (⟨.ret field, []⟩ : RSL.Obs B)) := by
    funext env
    rw [returned_exit decode r model source, silent env, fieldGraph]
  exact congrArg graph same
#print axioms closed_at
end AspisR1.NNG_EmittedPureCall
