import PV_B3P_FieldsVecPort15227
namespace PV_B3P_Fields15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 Result
set_option autoImplicit false

abbrev VecFieldState15 := core.result.Result Unit aspis_core.state_only_prefix.r0.Error × Bytes15

def fields_vec15 : Bytes15 → List U32 → Result VecFieldState15
  | out,[] => .ok (.Ok (),out)
  | out,value::rest =>
    if value ≥ 2147483647#u32 then .ok (.Err .Public,out)
    else do
      let next ← append_vec15 out value
      fields_vec15 next rest

def erase_vec_state15 (state : VecFieldState15) : FieldState13 := (state.1,state.2.val)

theorem fields_vec_reject15 (out : Bytes15) (value : U32) (rest : List U32)
    (bad : value ≥ 2147483647#u32) :
    fields_vec15 out (value::rest) = .ok (.Err .Public,out) := by
  simp only [fields_vec15,bad,if_true]

theorem fields_vec_projection15 (out : Bytes15) (values : List U32) :
    (do let state ← fields_vec15 out values; .ok (erase_vec_state15 state)) =
      fields_model13 append_bytes15 out.val values := by
  induction values generalizing out with
  | nil => rfl
  | cons value rest ih =>
    unfold fields_vec15 fields_model13
    by_cases bad : value ≥ 2147483647#u32
    · simp only [bad,if_true,bind_tc_ok,erase_vec_state15]
    · simp only [bad,if_false,PV_B3P_Ordered227.bind_assoc]
      have port := append_vec_projection15 out value
      cases operation : append_vec15 out value with
      | fail error =>
        simp only [operation,bind_tc_fail] at port ⊢
        rw [←port]
        rfl
      | div =>
        simp only [operation,bind_tc_div] at port ⊢
        rw [←port]
        rfl
      | ok next =>
        simp only [operation,bind_tc_ok] at port ⊢
        rw [←port]
        simpa only [bind_tc_ok] using ih next
#print axioms fields_vec_reject15
#print axioms fields_vec_projection15
end PV_B3P_Fields15227
