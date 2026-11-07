import PCM_Algebra
import PCM_ErrorMap
set_option autoImplicit false
namespace PCM.Computation
open RSL

theorem bind_pure {A B : Type} (a : A) (k : A → Computation B) :
    bind (pure a) k = k a := by
  funext s env o
  apply propext
  simp only [bind,pure,Observation.mk.injEq,Exit.ret.injEq,Prod.mk.injEq,
    Except.ok.injEq,List.nil_append]
  constructor
  · rintro (⟨a1,s1,es,o2,⟨⟨rfl,rfl⟩,rfl⟩,hk,ho⟩ | ⟨_,_,_,h,_⟩ | ⟨_,h,_⟩ | ⟨_,h,_⟩)
    · cases o2; simpa using ho ▸ hk
    · cases h.1.1
    · cases h.1
    · cases h.1
  · intro h
    exact Or.inl ⟨a,s,[],o,⟨⟨rfl,rfl⟩,rfl⟩,h,by cases o; rfl⟩

theorem bind_get {A : Type} (k : State → Computation A) :
    bind get k = (fun s env o => k s s env o) := by
  funext s env o
  change bind (pure s) k s env o = _
  rw [bind_pure]

theorem mapError_throw {A : Type} (f : ProgramError → ProgramError) (e : ProgramError) :
    mapError f (throw e : Computation A) = throw (f e) := by
  funext s env o
  apply propext
  constructor
  · rintro ⟨ro,hr,ho⟩
    change ro = ⟨.ret (.error e,s),[]⟩ at hr
    subst ro
    exact ho
  · intro h
    change o = ⟨.ret (.error (f e),s),[]⟩ at h
    subst o
    exact ⟨⟨.ret (.error e,s),[]⟩,rfl,rfl⟩

#print axioms bind_pure
#print axioms bind_get
#print axioms mapError_throw
end PCM.Computation
