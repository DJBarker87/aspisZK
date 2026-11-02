import PV_B3P_FieldsVecState15227
import PV_B3P_FrontierModel13227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std Result PV_B3P_Fields15227 PV_B3P_Binding13227
set_option autoImplicit false
/-- Ordered frontier calls with the actual Vec carrier. A Rust error retains
all preceding writes; outer fail/div is propagated at the original stage. -/
def frontier_vec557 : Bytes15 → List (List U32) → Result VecFieldState15
  | out, [] => .ok (.Ok (),out)
  | out, row::rows => do
      let (status,next) ← fields_vec15 out row
      match status with
      | .Err error => .ok (.Err error,next)
      | .Ok () => frontier_vec557 next rows

theorem frontier_vec_projection557 (out : Bytes15) (rows : List (List U32)) :
    (do let state ← frontier_vec557 out rows; .ok (erase_vec_state15 state)) =
      frontier_rows13 append_bytes15 out.val rows := by
  induction rows generalizing out with
  | nil => rfl
  | cons row rows ih =>
    have port := fields_vec_projection15 out row
    unfold frontier_vec557 frontier_rows13
    cases operation : fields_vec15 out row with
    | fail error =>
      simp only [operation,bind_tc_fail] at port ⊢
      rw [←port]
      rfl
    | div =>
      simp only [operation,bind_tc_div] at port ⊢
      rw [←port]
      rfl
    | ok state =>
      rcases state with ⟨status,next⟩
      simp only [operation,bind_tc_ok,erase_vec_state15] at port ⊢
      rw [←port]
      simp only [bind_tc_ok]
      cases status with
      | Err error => rfl
      | Ok value =>
        cases value
        exact ih next

/-- All 20 source frontier rows are retained in order. No canonical-word,
allocation-success, or success-only hypothesis is required by this port law. -/
theorem frontier_twenty_projection557 (out : Bytes15)
    (values : Array (Array U32 8#usize) 20#usize) :
    (do let state ← frontier_vec557 out (values.val.map (fun row => row.val))
        .ok (erase_vec_state15 state)) =
      frontier_rows13 append_bytes15 out.val (values.val.map (fun row => row.val)) :=
  frontier_vec_projection557 out _

#print axioms frontier_vec_projection557
#print axioms frontier_twenty_projection557
end PV_B3P_Closure557227
