import NMS_Interpreted
set_option autoImplicit false
namespace NMS_AllocPrefixes
open RSL

theorem at_site {A : Type} (next : Unit → Spec A) (env : Env) :
 Spec.bind Spec.alloc next env ⟨.abort,[]⟩ :=
 Or.inr (Or.inl ⟨[],Or.inr rfl,rfl⟩)

/-- An entered allocation can stop with exactly the prefix already observed,
regardless of a later source Err. No suffix or post-world is asserted. -/
theorem after_prefix {A B : Type} (first : Spec A) (next : A → Unit → Spec B)
 (env : Env) (a : A) (events : List Event)
 (prefixRun : first env ⟨.ret a,events⟩) :
 Spec.bind first (fun value => Spec.bind Spec.alloc (next value)) env ⟨.abort,events⟩ :=
 Or.inl ⟨a,events,⟨.abort,[]⟩,prefixRun,at_site (next a) env,by simp only [List.append_nil]⟩
#print axioms at_site
#print axioms after_prefix
end NMS_AllocPrefixes
