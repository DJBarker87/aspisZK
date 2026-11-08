import NNS_Fold241
set_option autoImplicit false
namespace NNS_SelectionObligation
open RSL

/-- Exact logical criterion for replacing a full relation by every law that
admits a particular function. This isolates the represented064 obligation;
it is not a new assumption in a delivered stage2 root. -/
theorem transport_iff {α : Type} (m : Spec α) (f : Env → Obs α) :
 (∀ w : Spec α, (∀ env, w env (f env)) →
  ∀ env o, m env o → w env o) ↔
 (∀ env o, m env o → o = f env) := by
 constructor
 · intro transport env o run
   exact transport (fun e z => z = f e) (fun _ => rfl) env o run
 · intro same w member env o run
   rw [same env o run]
   exact member env

/-- The exact domain-indexed version of the previous statement. Even when
all own-input clauses are proved, one selected function's law does not
transport other observations without this equality. -/
theorem packet_transport_iff {X α : Type} (dom : X → Prop)
 (m : X → Spec α) (f : X → Env → Obs α) :
 (∀ w : X → Spec α, (∀ x env, dom x → w x env (f x env)) →
  ∀ x env o, dom x → m x env o → w x env o) ↔
 (∀ x env o, dom x → m x env o → o = f x env) := by
 constructor
 · intro transport x env o domain run
   exact transport (fun y e z => z = f y e) (fun _ _ _ => rfl) x env o domain run
 · intro same w member x env o domain run
   rw [same x env o domain run]
   exact member x env domain

#print axioms transport_iff
#print axioms packet_transport_iff
end NNS_SelectionObligation
