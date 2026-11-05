import NHK_WordAssociation
set_option autoImplicit false
namespace AspisR1.NHK_WordReference
open Aeneas Aeneas.Std

/-- Reviewed transcription of the safe Rust NHK_word_ref used in the explicit
one-iteration proof_for_contract. Other cursor/candidate fields are covered by
the retained SAME-block native iterator certificate. -/
def reference (n d : Nat) (old candidate : U32) (reply : Bool) (window : Nat) :
    Bool × Nat × Nat × U32 :=
  let halt := decide (n=22 ∨ d=64)
  (halt,if halt || reply then n else n+1,
   if halt then d else d+1,
   if !halt && !reply && decide (window=n) then candidate else old)

theorem correspondence (s : NGQ_SamplerTrace.State) (x : U32) (cursor : Nat)
    (reply : Bool) (j : Fin 22) :
    reference s.accepted_len.val s.draws.val (NHB_Inactive.cell s.accepted j) x reply j.val =
      ((NHK_WordAssociation.G s x cursor reply j).stop,
       (NHK_WordAssociation.G s x cursor reply j).length,
       (NHK_WordAssociation.G s x cursor reply j).draws,
       (NHK_WordAssociation.G s x cursor reply j).word) := by rfl

/-- Contract pre-observations are always available from the SAME prestate.
They do not restrict a source caller or assume its successful output. -/
theorem pre_observations (s : NGQ_SamplerTrace.State) (j : Fin 22) :
    ∃ n d old, n=s.accepted_len.val ∧ d=s.draws.val ∧ old=NHB_Inactive.cell s.accepted j :=
  ⟨_,_,_,rfl,rfl,rfl⟩

#print axioms correspondence
#print axioms pre_observations
end AspisR1.NHK_WordReference
