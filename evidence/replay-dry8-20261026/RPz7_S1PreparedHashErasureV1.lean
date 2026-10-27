import RPz7_S1PreparedHashCodeV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

private theorem erase_digest_call {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (parts : Slice (Slice U8)) : erase (Code.digest D hash parts Code.done)=D.digest hash parts :=
  erase_digest D hash parts

theorem new_erasure {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (state : Array U8 32#usize) (variant : transport.Variant) :
    erase (PreparedHashEffects.new effects D hash state variant)=
      transcript.Transcript.new D hash state variant := by
  simp only [PreparedHashEffects.new,transcript.Transcript.new,effects,
    erase_bind,erase_lift,erase_digest_call,erase_pure]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_lift,erase_digest_call,erase_pure])
    | (apply bind_congr;intro x)

theorem absorb_erasure {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    erase (PreparedHashEffects.absorb effects D self row payload)=
      transcript.Transcript.absorb D self row payload := by
  simp only [PreparedHashEffects.absorb,transcript.Transcript.absorb,effects,
    erase_bind,erase_lift,erase_digest_call,erase_pure]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_lift,erase_digest_call,erase_pure])
    | (apply bind_congr;intro x)

theorem block_erasure {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    erase (PreparedHashEffects.block effects D self row payload)=
      transcript.Transcript.block D self row payload := by
  simp only [PreparedHashEffects.block,transcript.Transcript.block,effects,
    erase_bind,erase_lift,erase_digest_call,erase_pure,absorb_erasure]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_lift,erase_digest_call,erase_pure,absorb_erasure])
    | (apply bind_congr;intro x)

/-- The log retains attempted hash calls while its value projection is exactly
source evaluation, including fail/div. No oracle-query law is inferred here. -/
theorem block_run_value {H : Type} (D : aspis_core.Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    (run (PreparedHashEffects.block effects D self row payload)).2=
      transcript.Transcript.block D self row payload := by
  rw [run_value,block_erasure]

#print axioms new_erasure
#print axioms absorb_erasure
#print axioms block_erasure
#print axioms block_run_value
end AspisR1PublicPreparation.PreparedHashCode
