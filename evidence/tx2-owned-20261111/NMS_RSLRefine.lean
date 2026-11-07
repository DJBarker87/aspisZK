import RSL_TX2_241
set_option autoImplicit false
namespace NMS_RSLRefine
open RSL
/-- Observation inclusion keeps the exact return/error carrier and every
chronological prefix, including independent aborts and divergence. -/
def Refines {A : Type} (native model : Spec A) : Prop :=
 ∀ env observation, native env observation → model env observation

theorem refl {A : Type} (m : Spec A) : Refines m m := fun _ _ h => h

theorem trans {A : Type} {a b c : Spec A} (ab : Refines a b) (bc : Refines b c) :
 Refines a c := fun env o h => bc env o (ab env o h)

theorem bind {A B : Type} {m n : Spec A} {k l : A → Spec B}
 (first : Refines m n) (next : ∀ a, Refines (k a) (l a)) :
 Refines (Spec.bind m k) (Spec.bind n l) := by
 intro env o h
 rcases h with ⟨a,e1,o2,hm,hk,ho⟩ | ⟨e1,hm,ho⟩ | ⟨e1,hm,ho⟩
 · exact Or.inl ⟨a,e1,o2,first env _ hm,next a env _ hk,ho⟩
 · exact Or.inr (Or.inl ⟨e1,first env _ hm,ho⟩)
 · exact Or.inr (Or.inr ⟨e1,first env _ hm,ho⟩)

theorem rsbind {A B : Type} {m n : RS A} {k l : A → RS B}
 (first : Refines m n) (next : ∀ a, Refines (k a) (l a)) :
 Refines (RS.bind m k) (RS.bind n l) := by
 apply bind first
 intro reply
 cases reply with
 | ok a => exact next a
 | error e => exact refl _

theorem rsseq {B : Type} {m n : RS Unit} {k l : RS B}
 (first : Refines m n) (next : Refines k l) :
 Refines (RS.seq m k) (RS.seq n l) := rsbind first (fun _ => next)

/-- A deterministic actual child observation is substituted at the SAME
arguments/environment, using its complete packet, never just its Ok arm. -/
def observed {A B : Type} (native : A → Env → Obs B) (a : A) : Spec B :=
 fun env o => o = native a env

theorem call {A B : Type} (domain : A → Prop) (model : A → Spec B)
 (native : A → Env → Obs B)
 (packet : ∀ a env, domain a → model a env (native a env)) (a : A)
 (input : domain a) : Refines (observed native a) (Spec.call domain model a) := by
 intro env o ho
 subst o
 exact ⟨input,packet a env input⟩

/-- Bind inversion is only used inside the source path. It is not an
exported child-success or endpoint premise. -/
theorem rsbind_return {A B : Type} (m : RS A) (k : A → RS B)
 (env : Env) (b : B) (events : List Event)
 (run : RS.bind m k env ⟨.ret (.ok b), events⟩) :
 ∃ a prefix suffix, m env ⟨.ret (.ok a),prefix⟩ ∧
   k a env ⟨.ret (.ok b),suffix⟩ ∧ events = prefix ++ suffix := by
 rcases run with ⟨reply,prefix,o2,hm,hk,ho⟩ | ⟨_,_,ho⟩ | ⟨_,_,ho⟩
 · cases reply with
   | error e =>
     simp only [Spec.pure] at hk
     subst o2
     cases ho
   | ok a =>
     cases o2 with
     | mk exit suffix =>
       cases ho
       exact ⟨a,prefix,suffix,hm,hk,rfl⟩
 · cases ho
 · cases ho

theorem ofExcept_return {A : Type} (reply : Except ProgramError A)
 (env : Env) (a : A) (events : List Event)
 (run : RS.ofExcept reply env ⟨.ret (.ok a),events⟩) : reply = .ok a := by
 have h := congrArg Obs.exit run
 exact (Exit.ret.inj h).symm

#print axioms refl
#print axioms trans
#print axioms bind
#print axioms rsbind
#print axioms rsseq
#print axioms call
#print axioms rsbind_return
#print axioms ofExcept_return
end NMS_RSLRefine
