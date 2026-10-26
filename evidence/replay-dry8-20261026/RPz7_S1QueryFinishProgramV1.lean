import RPz7_S1PreparedSilentCodeV1
import RPz7_S1QueryModelContinuationV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result ControlFlow
open PreparedHashCode
open AspisV8R19.MemoizedProgramLaw

private theorem bind_congr {A B : Type} (p : Result A) (f g : A → Result B)
    (h : ∀ a, f a=g a) : (p >>= f)=(p >>= g) :=
  congrArg (fun next => p >>= next) (funext h)

/-- Explicit source decoder/embed/trace continuation emits no digest nodes.
No purity assertion about an unextracted native callback is inferred here. -/
theorem finish_silent (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (absorbed : transcript.Transcript H) (blocks advances : Blocks8) :
    Silent (finish (M := Code) B D absorbed blocks advances) := by
  unfold finish
  repeat' first
    | (solve | with_reducible apply silent_lift)
    | (solve | with_reducible apply silent_pure)
    | with_reducible apply silent_bind
    | intro x
    | split

theorem finish_erasure (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (absorbed : transcript.Transcript H) (blocks advances : Blocks8) :
    erase (finish (M := Code) B D absorbed blocks advances)=
      finish (M := Result) B D absorbed blocks advances := by
  unfold finish
  repeat' first
    | (rw [erase_bind,erase_lift]; apply bind_congr; intro x)
    | (exact erase_pure _)
    | rfl
    | split

theorem finish_program (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (absorbed : transcript.Transcript H) (blocks advances : Blocks8) :
    oracleProgram (finish (M := Code) B D absorbed blocks advances)=
      Program.done (finish (M := Result) B D absorbed blocks advances) := by
  rw [oracleProgram_silent _ (finish_silent B D absorbed blocks advances),finish_erasure]

#print axioms finish_silent
#print axioms finish_erasure
#print axioms finish_program
end AspisR1PublicPreparation.PreparedQueryMaterialize
