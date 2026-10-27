import RPz7_S1PreparedScalarEffectsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

private theorem erase_if {A : Type} (p : Prop) [Decidable p] (yes no : Code A) :
    erase (if p then yes else no)=(if p then erase yes else erase no) := by split <;> rfl

theorem scalar_erasure (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
    erase (PreparedScalarEffects.scalar effects B D self row payload nonzero)=
      PreparedModel.scalar B D self row payload nonzero := by
  simp only [PreparedScalarEffects.scalar,PreparedModel.scalar,
    erase_bind,erase_lift,erase_pure,block_erasure,erase_if]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_lift,erase_pure,block_erasure,erase_if])
    | (apply bind_congr;intro x)
    | split

theorem scalar_k_erasure (B : PreparedModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    erase (PreparedScalarEffects.scalar_k effects B D self row payload)=
      PreparedModel.scalar_k B D self row payload := by
  simp only [PreparedScalarEffects.scalar_k,PreparedModel.scalar_k,
    erase_bind,erase_lift,erase_pure,block_erasure]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_lift,erase_pure,block_erasure])
    | (apply bind_congr;intro x)

#print axioms scalar_erasure
#print axioms scalar_k_erasure
end AspisR1PublicPreparation.PreparedHashCode
