import R1Z.PV_RunJoin_CircleNeutralFinite53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralSquareCell53
theorem owned (r after : core.ops.range.Range Usize) (a : U32)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize r = ok (some r.start,after)) :
    PV_RunJoin_CircleRawScalar52.field.square_n_loop.body r a = (do
      let v ← PV_RunJoin_CircleRawScalar52.field.M31.mul a a
      ok (cont (after,v))) := by
  unfold PV_RunJoin_CircleRawScalar52.field.square_n_loop.body
  rw [hn]
  rfl

theorem model (r after : core.ops.range.Range Usize) (a : U32)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize r = ok (some r.start,after)) :
    PV_RunJoin_CircleR72Raw52.field.square_n_loop.body r a = (do
      let v ← PV_RunJoin_CircleR72Raw52.field.M31.mul a a
      ok (cont (after,v))) := by
  unfold PV_RunJoin_CircleR72Raw52.field.square_n_loop.body
  rw [hn]
  rfl

#print axioms owned
#print axioms model
end R1Z.PV_RunJoin_CircleNeutralSquareCell53
