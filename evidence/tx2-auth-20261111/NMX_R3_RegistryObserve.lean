import NMX_R3_RegistryRun
set_option autoImplicit false
namespace NMX_R3_RegistryObserve
open RSL

def map {A B : Type} (f : A → B) (o : Obs A) : Obs B :=
 ⟨match o.exit with | .ret a => .ret (f a) | .abort => .abort | .diverge => .diverge,o.events⟩

theorem sound {A B : Type} (f : A → B) (m : Spec A) (env : Env) (o : Obs A) (h : m env o) :
 Spec.map f m env (map f o) := by
 rcases o with ⟨exit,events⟩
 cases exit with
 | ret a => exact Or.inl ⟨a,events,⟨.ret (f a),[]⟩,h,rfl,by simp only [map,List.append_nil]⟩
 | abort => exact Or.inr (Or.inl ⟨events,h,rfl⟩)
 | diverge => exact Or.inr (Or.inr ⟨events,h,rfl⟩)
#print axioms sound
end NMX_R3_RegistryObserve
