import NMX_R5_Native242
set_option autoImplicit false
namespace NMX_R8_SimulatesPath
open RSL NMS_R2N_Interpreted

theorem bind_using {A B C D : Type} (value : A → C) (output : B → D)
 (actual : Spec A) (model : Spec C) (next : A → Spec B) (later : C → Spec D)
 (first : Simulates value actual model)
 (rest : ∀ env a events, actual env ⟨.ret a,events⟩ →
   ∀ o, next a env o → later (value a) env (mapObs output o)) :
 Simulates output (Spec.bind actual next) (Spec.bind model later) := by
 intro env observation run
 rcases run with ⟨a,events,nextObs,hfirst,hlast,same⟩ | ⟨events,hfirst,same⟩ | ⟨events,hfirst,same⟩
 · subst observation
   exact Or.inl ⟨value a,events,mapObs output nextObs,first env _ hfirst,
    rest env a events hfirst nextObs hlast,rfl⟩
 · subst observation
   exact Or.inr (Or.inl ⟨events,first env _ hfirst,rfl⟩)
 · subst observation
   exact Or.inr (Or.inr ⟨events,first env _ hfirst,rfl⟩)

/-- Infallible native std step viewed in the Rust-Result reference layer. -/
theorem infallible {A B C D : Type} (value : A → C) (output : B → Except ProgramError D)
 (actual : Spec A) (model : RS C) (next : A → Spec B) (later : C → RS D)
 (first : Simulates (fun a => Except.ok (value a)) actual model)
 (rest : ∀ a, Simulates output (next a) (later (value a))) :
 Simulates output (Spec.bind actual next) (RS.bind model later) := by
 apply NMS_R2N_Interpreted.bind (fun a => Except.ok (value a)) output _ _ _ _ first
 intro a
 exact rest a
#print axioms bind_using
#print axioms infallible
end NMX_R8_SimulatesPath
