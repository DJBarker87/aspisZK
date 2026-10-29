import R1Z.PV_RunJoin_CircleNeutralFinite53
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralSquareEquation53
theorem owned (r : core.ops.range.Range Usize) (a : U32) :
    PV_RunJoin_CircleRawScalar52.field.square_n_loop r a = (do
      let cf ← PV_RunJoin_CircleRawScalar52.field.square_n_loop.body r a
      match cf with
      | .cont next => PV_RunJoin_CircleRawScalar52.field.square_n_loop next.1 next.2
      | .done out => ok out) := by
  unfold PV_RunJoin_CircleRawScalar52.field.square_n_loop
  rw [ProverRw19LoopBind.loop_bind]
  rfl

theorem model (r : core.ops.range.Range Usize) (a : U32) :
    PV_RunJoin_CircleR72Raw52.field.square_n_loop r a = (do
      let cf ← PV_RunJoin_CircleR72Raw52.field.square_n_loop.body r a
      match cf with
      | .cont next => PV_RunJoin_CircleR72Raw52.field.square_n_loop next.1 next.2
      | .done out => ok out) := by
  unfold PV_RunJoin_CircleR72Raw52.field.square_n_loop
  rw [ProverRw19LoopBind.loop_bind]
  rfl

#print axioms owned
#print axioms model
end R1Z.PV_RunJoin_CircleNeutralSquareEquation53
