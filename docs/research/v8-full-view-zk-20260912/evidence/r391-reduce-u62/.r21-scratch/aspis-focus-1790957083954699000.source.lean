import AspisR388ReduceU62.Funs
import AspisV8R19.R161WrappedMulExecution

set_option autoImplicit false
namespace AspisV8R19.R391ReduceU62Execution
open Aeneas Aeneas.Std Result

/-- The exact generated helper definition unfolds to the frozen field reducer. -/
theorem generated_reduce_u64_eq_frozen (x : U64) :
    AspisR388ReduceU62.aspis_core.field.reduce_u64 x =
      AspisR156FullFreeze.aspis_core.field.reduce_u64 x := by
  rfl

/-- The generated release wrapper agrees with the retained M31 reducer wrapper. -/
theorem generated_reduce_u62_eq_frozen (x : U64) :
    AspisR388ReduceU62.aspis_core.field.M31.reduce_u62 x =
      AspisR156FullFreeze.aspis_core.field.M31.reduce_u64 x := by
  simp only [AspisR388ReduceU62.aspis_core.field.M31.reduce_u62,
    AspisR156FullFreeze.aspis_core.field.M31.reduce_u64,
    generated_reduce_u64_eq_frozen, bind_tc_ok]

/-- The extracted release wrapper succeeds canonically for every U64 input. -/
theorem generated_reduce_u62_success (x : U64) :
    ∃ z : U32,
      AspisR388ReduceU62.aspis_core.field.M31.reduce_u62 x = .ok z ∧
      z.val = x.val % AspisV8R17.RawReducer.P ∧ z.val < AspisV8R17.RawReducer.P := by
  rw [generated_reduce_u62_eq_frozen]
  simpa only [AspisR156FullFreeze.aspis_core.field.M31.reduce_u64, bind_tc_ok] using
    AspisV8R19.R161WrappedMulExecution.reducer_success x

/-- The extracted release wrapper has the exact retained M31 encoding. -/
theorem generated_reduce_u62_encode (x : U64) :
    AspisR388ReduceU62.aspis_core.field.M31.reduce_u62 x =
      .ok (AspisV8R15.ExactTowerBase.encodeBase
        (x.val : AspisV8R15.ExactTowerBase.M31Exact)) := by
  rw [generated_reduce_u62_eq_frozen]
  exact AspisV8R19.R161WrappedMulExecution.reduce_encode x

#print axioms AspisR388ReduceU62.aspis_core.field.reduce_u64
#print axioms AspisR388ReduceU62.aspis_core.field.M31.reduce_u62
#print axioms generated_reduce_u64_eq_frozen
#print axioms generated_reduce_u62_eq_frozen
#print axioms generated_reduce_u62_success
#print axioms generated_reduce_u62_encode

end AspisV8R19.R391ReduceU62Execution
