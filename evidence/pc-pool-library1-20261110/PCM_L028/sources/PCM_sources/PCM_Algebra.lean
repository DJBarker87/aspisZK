import PCM_Semantics
set_option autoImplicit false
namespace PCM.Computation
open RSL

theorem bind_throw {A B : Type} (e : ProgramError) (k : A → Computation B) :
    bind (throw e) k = throw e := by
  funext s env o
  apply propext
  simp only [bind, throw, Observation.mk.injEq, RSL.Exit.ret.injEq, Prod.mk.injEq,
    Except.error.injEq, List.nil_append]
  constructor
  · rintro (⟨a,s1,es,o2,h,_,_⟩ | ⟨e1,s1,es,h,ho⟩ | ⟨es,h,_⟩ | ⟨es,h,_⟩)
    · cases h.1.1
    · rcases h with ⟨⟨rfl,rfl⟩,rfl⟩; exact ho
    · cases h.1
    · cases h.1
  · intro h
    exact Or.inr (Or.inl ⟨e,s,[],⟨⟨rfl,rfl⟩,rfl⟩,h⟩)

/-- Early child rejection proves a complete parent counterexample without
assuming a successful execution or discarding an effect prefix. -/
theorem early_reject {A B : Type} (c : PCM.Child A B) (a : A)
    (e : ProgramError) (k : B → Computation Unit)
    (law : c.call a = throw e) : bind (c.call a) k = throw e := by
  rw [law,bind_throw]

#print axioms bind_throw
#print axioms early_reject
end PCM.Computation
