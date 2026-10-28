import NCO_LoopSteps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ValidatorTail

theorem zero_div : (0#usize / 32#usize : Result Usize) = ok 0#usize := by
  obtain ⟨x,hx,hv⟩ := UScalar.div_spec (0#usize) (y := 32#usize) (by scalar_tac)
  rw [hx]
  exact congrArg ok (UScalar.eq_of_val_eq (by simpa using hv))

theorem empty (row : U8) (payload : Slice U8) (len : payload.val.length = 0) :
    NCO_ParserRef.validate_ref row payload = ok (.Ok ()) := by
  have length : Slice.len payload = 0#usize := by scalar_tac
  have step : NCO_ParserRef.validate_ref_loop0.body payload 0#usize =
      ok (.done (0#usize, some (.Ok ()))) :=
    NCO_LoopSteps.outer_done payload 0#usize 0#usize (by rw [length]; exact zero_div) (by omega)
  unfold NCO_ParserRef.validate_ref NCO_ParserRef.validate_ref_loop0
  rw [NCO_LoopSteps.loop_done _ _ _ step]
  rfl

#print axioms zero_div
#print axioms empty
end NCO_ValidatorTail
