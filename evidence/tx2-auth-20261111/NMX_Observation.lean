import RSL_Base
set_option autoImplicit false
namespace NMX_Observation
open RSL
/-- Actual returned observations concatenate only the reached prefix. Stops
have no continuation, allocator post-state, or invented cleanup. -/
def bind {A B : Type} (first : Obs A) (next : A → Obs B) : Obs B :=
 match first.exit with
 | .ret a => let tail := next a; ⟨tail.exit,first.events ++ tail.events⟩
 | .abort => ⟨.abort,first.events⟩
 | .diverge => ⟨.diverge,first.events⟩

def rustBind {A B : Type} (first : Obs (Except ProgramError A))
 (next : A → Obs (Except ProgramError B)) : Obs (Except ProgramError B) :=
 bind first (fun reply => match reply with
 | .ok a => next a
 | .error e => ⟨.ret (.error e),[]⟩)

theorem bind_sound {A B : Type} (first : Obs A) (next : A → Obs B)
 (reference : Spec A) (continuation : A → Spec B) (env : Env)
 (head : reference env first) (tail : ∀ a, continuation a env (next a)) :
 Spec.bind reference continuation env (bind first next) := by
 cases first with
 | mk exit events =>
  cases exit with
  | ret a => exact Or.inl ⟨a,events,next a,head,tail a,rfl⟩
  | abort => exact Or.inr (Or.inl ⟨events,head,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨events,head,rfl⟩)

theorem rust_sound {A B : Type} (first : Obs (Except ProgramError A))
 (next : A → Obs (Except ProgramError B))
 (reference : RS A) (continuation : A → RS B) (env : Env)
 (head : reference env first) (tail : ∀ a, continuation a env (next a)) :
 RS.bind reference continuation env (rustBind first next) := by
 apply bind_sound first _ reference _ env head
 intro reply
 cases reply with
 | error e => rfl
 | ok a => exact tail a

theorem abort_prefix {A B : Type} (events : List Event) (next : A → Obs B) :
 bind ⟨.abort,events⟩ next = ⟨.abort,events⟩ := rfl

theorem error_prefix {A B : Type} (events : List Event) (e : ProgramError)
 (next : A → Obs (Except ProgramError B)) :
 rustBind ⟨.ret (.error e),events⟩ next = ⟨.ret (.error e),events⟩ := by
 simp only [rustBind,bind,List.append_nil]
#print axioms bind_sound
#print axioms rust_sound
#print axioms abort_prefix
#print axioms error_prefix
end NMX_Observation
