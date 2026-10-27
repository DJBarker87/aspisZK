import R1Z.PV_RunJoin_StoreContinuationResidual
import R1Z.ProverRwOuterMapErr
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MapErrInstalled
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Pure source implementation of map_err, installed by the sibling selector.
The equality is the precise dictionary identity obligation for other selectors. -/
def Identity (ops : ExternalFuns) : Prop := @ExternalFuns.op12 _ ops = @ProverRwOuterMapErr.map_err

theorem pure_parametric {S T E F A : Type}
    (left : core.ops.function.FnOnce S E F) (right : core.ops.function.FnOnce T E F)
    (s : S) (t : T) (value : core.result.Result A E)
    (same : ∀ e, left.call_once s e = right.call_once t e) :
    ProverRwOuterMapErr.map_err left value s =
      ProverRwOuterMapErr.map_err right value t := by
  cases value with
  | Ok a => rfl
  | Err e => simp only [ProverRwOuterMapErr.map_err, same]

theorem installed (ops : ExternalFuns) (identity : Identity ops) :
    @PV_RunJoin_StoreContinuationResidual.MapErrParametric _ ops := by
  intro S T E F left right s t A value same
  change ops.op12 left value s = ops.op12 right value t
  change @ExternalFuns.op12 _ ops = @ProverRwOuterMapErr.map_err at identity
  rw [identity]
  exact pure_parametric left right s t value same

theorem selected (ops : ExternalFuns) : Identity (ProverRwOuterMapErr.selected ops) := rfl

#print axioms pure_parametric
#print axioms installed
#print axioms selected
end R1Z.PV_RunJoin_MapErrInstalled
