import PCM_StepLaws
set_option autoImplicit false
namespace PCM.Computation
open RSL
/-- A forbidden returned error cannot be hidden by an earlier abort prefix. -/
def Avoid {A : Type} (e : ProgramError) (m : Computation A) : Prop :=
  ∀ s env s1 events, ¬ m s env ⟨.ret (.error e,s1),events⟩

theorem pure_avoid {A : Type} (e : ProgramError) (a : A) : Avoid e (pure a) := by
  intro s env s1 events h
  have he := congrArg Observation.exit h
  cases he

theorem alloc_avoid (e : ProgramError) : Avoid e alloc := by
  intro s env s1 events h
  rcases h with ⟨ro,hr,he⟩
  have hh := (RSL.RS.lift_alloc_iff env ro).mp hr
  rcases hh with rfl | rfl <;> cases he

theorem mapError_avoid {A : Type} (bad target : ProgramError) (h : bad ≠ target)
    (m : Computation A) : Avoid bad (mapError (fun _ => target) m) := by
  intro s env s1 events hm
  rcases hm with ⟨ro,_,he⟩
  cases hx : ro.exit with
  | abort => simp only [hx] at he; cases he
  | diverge => simp only [hx] at he; cases he
  | ret pair =>
    rcases pair with ⟨reply,post⟩
    cases reply with
    | ok a => simp only [hx] at he; cases he
    | error e =>
      have hh := congrArg Observation.exit he
      simp only [hx] at hh
      have hc := Except.error.inj (congrArg Prod.fst (Exit.ret.inj hh))
      exact h hc

theorem bind_avoid {A B : Type} (bad : ProgramError) (m : Computation A)
    (k : A → Computation B) (hm : Avoid bad m) (hk : ∀ a, Avoid bad (k a)) :
    Avoid bad (bind m k) := by
  intro s env s1 events h
  rcases h with ⟨a,s2,es,o2,h1,h2,ho⟩ | ⟨e,s2,es,h1,ho⟩ | ⟨es,_,ho⟩ | ⟨es,_,ho⟩
  · have he := congrArg Observation.exit ho
    have hp : o2.exit = .ret (.error bad,s1) := he.symm
    cases o2 with
    | mk ex ev =>
      dsimp only at hp
      subst ex
      exact hk a s2 env s1 ev h2
  · have he := congrArg Observation.exit ho
    have hp := congrArg Prod.fst (Exit.ret.inj he)
    have hh := Except.error.inj hp
    subst e
    exact hm s env s2 es h1
  · cases congrArg Observation.exit ho
  · cases congrArg Observation.exit ho

#print axioms pure_avoid
#print axioms alloc_avoid
#print axioms mapError_avoid
#print axioms bind_avoid
end PCM.Computation
