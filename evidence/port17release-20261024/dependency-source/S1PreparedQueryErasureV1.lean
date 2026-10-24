import S1PreparedQueryEffectsV1
import S1PreparedScalarErasureV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result ControlFlow

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a, f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- Exact original query execution, including all materialized digest calls,
all rejection outcomes, and the selected returned transcript state. -/
theorem queries_erasure (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    erase (PreparedQueryEffects.queries effects B D self row payload)=
      QueriesModel.queries B D self row payload := by
  unfold PreparedQueryEffects.queries QueriesModel.queries
  repeat' first
    | (rw [erase_bind]
       first | rw [erase_lift] | rw [erase_digest] | rw [absorb_erasure]
       apply bind_congr
       intro x)
    | (apply bind_congr; intro x)
    | (exact erase_pure _)
    | rfl
    | split

theorem queries_run_value (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    (run (PreparedQueryEffects.queries effects B D self row payload)).2=
      QueriesModel.queries B D self row payload := by
  rw [run_value,queries_erasure]

#print axioms queries_erasure
#print axioms queries_run_value
end AspisR1PublicPreparation.PreparedHashCode
