import RSL_TX1_345
-- Canonical rev4 retarget of NMT_345Observation generic sequencing.
set_option autoImplicit false
namespace AspisR1.NNG_Obs345
open RSL
/-- Exact observation sequencing. A nonreturning child has only its prefix;
there is no invented post-world or suffix action. -/
def bindObs {A B : Type} (m : Obs A) (next : A → Obs B) : Obs B :=
 match m.exit with
 | .ret a => let n := next a; ⟨n.exit,m.events ++ n.events⟩
 | .abort => ⟨.abort,m.events⟩
 | .diverge => ⟨.diverge,m.events⟩

theorem bind_valid {A B : Type} (m : Spec A) (k : A → Spec B)
 (actual : Obs A) (next : A → Obs B) (env : Env)
 (first : m env actual) (later : ∀ a, k a env (next a)) :
 Spec.bind m k env (bindObs actual next) := by
 cases actual with
 | mk exit events =>
  cases exit with
  | ret a => exact Or.inl ⟨a,events,next a,first,later a,rfl⟩
  | abort => exact Or.inr (Or.inl ⟨events,first,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨events,first,rfl⟩)

def tryObs {A B : Type} (m : Obs (Except ProgramError A))
 (next : A → Obs (Except ProgramError B)) : Obs (Except ProgramError B) :=
 bindObs m (fun r => match r with
 | .ok a => next a
 | .error e => ⟨.ret (.error e),[]⟩)

theorem try_valid {A B : Type} (m : RS A) (k : A → RS B)
 (actual : Obs (Except ProgramError A)) (next : A → Obs (Except ProgramError B))
 (env : Env) (first : m env actual) (later : ∀ a,k a env (next a)) :
 RS.bind m k env (tryObs actual next) := by
 apply bind_valid _ _ actual _ env first
 intro r
 cases r with
 | ok a => exact later a
 | error e => rfl

theorem abort_prefix {A B : Type} (prefixEvents : List Event) (next : A → Obs B) :
 bindObs ⟨.abort,prefixEvents⟩ next = ⟨.abort,prefixEvents⟩ := rfl

theorem diverge_prefix {A B : Type} (prefixEvents : List Event) (next : A → Obs B) :
 bindObs ⟨.diverge,prefixEvents⟩ next = ⟨.diverge,prefixEvents⟩ := rfl


#print axioms bind_valid
#print axioms try_valid
#print axioms abort_prefix
#print axioms diverge_prefix
end AspisR1.NNG_Obs345
