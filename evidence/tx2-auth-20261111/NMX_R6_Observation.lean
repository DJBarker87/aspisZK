import NMX_R5_Decode242
set_option autoImplicit false
noncomputable section
namespace NMX_R6_Observation
open Aeneas Aeneas.Std Result

def scalar {A : Type} : Result A → RSL.Obs A
 | .ok a => ⟨.ret a,[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

def bind {A B : Type} (o : RSL.Obs A) (k : A → RSL.Obs B) : RSL.Obs B :=
 match o.exit with
 | .ret a => let later := k a; ⟨later.exit,o.events ++ later.events⟩
 | .abort => ⟨.abort,o.events⟩
 | .diverge => ⟨.diverge,o.events⟩

def rsbind {A B : Type} (o : RSL.Obs (Except RSL.ProgramError A))
 (k : A → RSL.Obs (Except RSL.ProgramError B)) :=
 bind o (fun r => match r with | .ok a => k a | .error e => ⟨.ret (.error e),[]⟩)

theorem member {A B : Type} (first : RSL.Spec A) (next : A → RSL.Spec B)
 (env : RSL.Env) (o : RSL.Obs A) (k : A → RSL.Obs B)
 (hf : first env o) (hk : ∀ a, next a env (k a)) :
 RSL.Spec.bind first next env (bind o k) := by
 cases o with
 | mk exit events =>
  cases exit with
  | ret a => exact Or.inl ⟨a,events,k a,hf,hk a,rfl⟩
  | abort => exact Or.inr (Or.inl ⟨events,hf,rfl⟩)
  | diverge => exact Or.inr (Or.inr ⟨events,hf,rfl⟩)

theorem rsmember {A B : Type} (first : RSL.RS A) (next : A → RSL.RS B)
 (env : RSL.Env) (o : RSL.Obs (Except RSL.ProgramError A))
 (k : A → RSL.Obs (Except RSL.ProgramError B))
 (hf : first env o) (hk : ∀ a, next a env (k a)) :
 RSL.RS.bind first next env (rsbind o k) := by
 apply member first _ env o _ hf
 intro r
 cases r with
 | ok a => exact hk a
 | error e => rfl

def Complete {A : Type} (meaning : RSL.Spec A) (code : Result A) : Prop :=
 ∀ env, meaning env (scalar code)

theorem lift {A : Type} (code : Result A) : Complete (NMS_R2N_Interpreted.liftResult code) code := by
 intro env
 cases code <;> rfl

theorem scalar_bind {A B : Type} (code : Result A) (next : A → Result B) :
 scalar (code >>= next) = bind (scalar code) (fun a => scalar (next a)) := by
 cases code <;> rfl

theorem complete_bind {A B : Type} (first : RSL.Spec A) (code : Result A)
 (next : A → RSL.Spec B) (source : A → Result B)
 (hf : Complete first code) (hk : ∀ a, Complete (next a) (source a)) :
 Complete (RSL.Spec.bind first next) (code >>= source) := by
 intro env
 rw [scalar_bind]
 exact member first next env _ _ (hf env) (fun a => hk a env)

theorem allocate : Complete RSL.Spec.alloc (ok ()) := by
 intro env
 exact Or.inl rfl

theorem branch {A : Type} (b : Bool) (yes no : RSL.Spec A) (y n : Result A)
 (hy : Complete yes y) (hn : Complete no n) :
 Complete (if b then yes else no) (if b then y else n) := by
 cases b <;> assumption

#print axioms member
#print axioms rsmember
#print axioms lift
#print axioms scalar_bind
#print axioms complete_bind
#print axioms allocate
#print axioms branch
end NMX_R6_Observation
end
