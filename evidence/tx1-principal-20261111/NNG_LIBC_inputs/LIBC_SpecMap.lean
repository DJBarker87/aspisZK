import LIB_Carriers
set_option autoImplicit false
namespace LIBC_SpecMap
open RSL
def observation {A B : Type} (f : A → B) (o : Obs A) : Obs B :=
 ⟨(match o.exit with | .ret a => .ret (f a) | .abort => .abort | .diverge => .diverge),o.events⟩
theorem exact {A B : Type} (f : A → B) (m : Spec A) (env : Env) (o : Obs B) :
 Spec.map f m env o ↔ ∃ source, m env source ∧ o = observation f source := by
 constructor
 · intro h
   rcases h with ⟨a,ev,o2,hm,hp,ho⟩ | ⟨ev,hm,ho⟩ | ⟨ev,hm,ho⟩
   · subst o2
     refine ⟨⟨.ret a,ev⟩,hm,?_⟩
     simpa only [observation,List.append_nil] using ho
   · exact ⟨⟨.abort,ev⟩,hm,ho⟩
   · exact ⟨⟨.diverge,ev⟩,hm,ho⟩
 · rintro ⟨⟨exit,ev⟩,hm,ho⟩
   subst o
   cases exit with
   | ret a =>
     exact Or.inl ⟨a,ev,⟨.ret (f a),[]⟩,hm,rfl,by simp only [observation,List.append_nil]⟩
   | abort => exact Or.inr (Or.inl ⟨ev,hm,rfl⟩)
   | diverge => exact Or.inr (Or.inr ⟨ev,hm,rfl⟩)
theorem result {A B C : Type} (f : A → B) (g : B → C) (events : List Event)
 (r : Aeneas.Std.Result A) :
 observation g (LIB_Carriers.resultObs f events r) = LIB_Carriers.resultObs (g ∘ f) events r := by
 cases r <;> rfl
#print axioms exact
#print axioms result
end LIBC_SpecMap
