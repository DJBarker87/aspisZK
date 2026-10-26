import SAG_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_Freedom
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
abbrev Model := AspisWideTower.WideExact
variable {W : Type}

/-- A data-only FinishOps slot permits any successful evaluator; release does
not constrain its meaning. This is an interface countermodel, not shipped code. -/
def wrongEval (seed : FinishOps W) (poly : Polynomial Model) : FinishOps W :=
  {seed with polynomial := fun _ alpha =>
    ok (CheckpointBytes4ReaderFields.sourceE (poly.eval (CheckpointBytes5Output.ofE alpha) + 1))}

theorem wrongEval_returns (seed : FinishOps W) (poly : Polynomial Model)
    (bytes : Slice U8) (alpha : E) :
    (Port3_FinishStage.release (wrongEval seed poly)).polynomial bytes alpha =
      ok (CheckpointBytes4ReaderFields.sourceE
        (poly.eval (CheckpointBytes5Output.ofE alpha) + 1)) := rfl

theorem evaluator_not_forced (seed : FinishOps W) (poly : Polynomial Model)
    (bytes : Slice U8) (alpha : E) :
    ¬ (∀ a value,
      (Port3_FinishStage.release (wrongEval seed poly)).polynomial bytes a = ok value →
      CheckpointBytes5Output.ofE value = poly.eval (CheckpointBytes5Output.ofE a)) := by
  intro law
  have bad := law alpha _ (wrongEval_returns seed poly bytes alpha)
  rw [CheckpointBytes5Output.ofE_source] at bad
  have : (1 : Model) = 0 := add_left_cancel (bad.trans (add_zero _).symm)
  exact one_ne_zero this

#print axioms wrongEval_returns
#print axioms evaluator_not_forced
end AspisR1.SAG_Freedom
end
