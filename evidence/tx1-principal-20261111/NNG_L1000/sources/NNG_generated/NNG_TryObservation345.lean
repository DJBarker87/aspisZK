import NNG_Tree345
import NNG_ObservationAlgebra
import NNG_Observe345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TryObservation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

/-- Source `?` composition at the original native reply, including both
nonreturning prefixes. The continuation obligation is reached-only. -/
theorem checked {A B : Type} (f : A → B) (r : Result (core.result.Result A PE))
 (next : A → Code Ret) (m : RSL.RS B) (k : B → RSL.RS RSL.Bytes)
 (events : Event → List RSL.Event) (env : RSL.Env)
 (first : m env (NNG_Observe345.observe f r))
 (later : ∀ a, r=ok (.Ok a) → k (f a) env
  (observation NNG_ChildSource345.port events (next a))) :
 RSL.RS.bind m k env (observation NNG_ChildSource345.port events
  (NNG_TreeBase345.tryCode r next)) := by
 cases r with
 | fail e => exact Or.inr (Or.inl ⟨[],first,rfl⟩)
 | div => exact Or.inr (Or.inr ⟨[],first,rfl⟩)
 | ok reply =>
  cases reply with
  | Err e => exact Or.inl ⟨.error (pe e),[],⟨.ret (.error (pe e)),[]⟩,first,rfl,rfl⟩
  | Ok a => exact Or.inl ⟨.ok (f a),[],observation NNG_ChildSource345.port events (next a),first,later a rfl,rfl⟩
#print axioms checked
end AspisR1.NNG_TryObservation345
