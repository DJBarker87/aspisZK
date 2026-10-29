import PV_B3P_PartsBinding13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
/-- Allocation-sensitive append is an explicit port, not an assumption that
Vec operations cannot abort. The Result state retains partial writes on Err. -/
abbrev AppendWord13 := List U8 → U32 → Result (List U8)
abbrev FieldState13 := core.result.Result Unit aspis_core.state_only_prefix.r0.Error × List U8

def fields_model13 (append : AppendWord13) : List U8 → List U32 → Result FieldState13
  | out, [] => .ok (.Ok (),out)
  | out, value::values =>
    if value ≥ 2147483647#u32 then .ok (.Err .Public,out)
    else do
      let out1 ← append out value
      fields_model13 append out1 values

def PV_B3P_Link_fields (append : AppendWord13)
    (source : List U8 → List U32 → Result FieldState13) : Prop :=
  source = fields_model13 append

theorem fields_reject13 (append : AppendWord13) (out : List U8)
    (value : U32) (values : List U32) (bad : value ≥ 2147483647#u32) :
    fields_model13 append out (value::values) = .ok (.Err .Public,out) := by
  simp only [fields_model13,bad,if_true]

theorem fields_append_fail13 (append : AppendWord13) (out : List U8)
    (value : U32) (values : List U32) (good : ¬value ≥ 2147483647#u32)
    (error : Aeneas.Std.Error) (failed : append out value = .fail error) :
    fields_model13 append out (value::values) = .fail error := by
  simp only [fields_model13,good,if_false,failed,bind_tc_fail]

theorem fields_append_div13 (append : AppendWord13) (out : List U8)
    (value : U32) (values : List U32) (good : ¬value ≥ 2147483647#u32)
    (diverges : append out value = .div) :
    fields_model13 append out (value::values) = .div := by
  simp only [fields_model13,good,if_false,diverges,bind_tc_div]

/-- Model-instance witness only; native Vec association is still a Link. -/
theorem fields_model_witness13 (append : AppendWord13) :
    ∃ source, PV_B3P_Link_fields append source := ⟨fields_model13 append,rfl⟩
#print axioms fields_reject13
#print axioms fields_append_fail13
#print axioms fields_append_div13
#print axioms fields_model_witness13
end PV_B3P_Binding13227
