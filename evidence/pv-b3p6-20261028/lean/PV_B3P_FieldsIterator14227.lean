import PV_B3P_FieldsModel13227
namespace PV_B3P_Fields14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 Result ControlFlow
set_option autoImplicit false
/-- Value view of an immutable forward slice iterator. The unread suffix is
unchanged by the append port, whose only mutable loan is the output Vec. -/
def field_next14 : List U32 → Option U32 × List U32
  | [] => (none,[])
  | value::rest => (some value,rest)

def fields_body14 (append : AppendWord13) (state : List U8 × List U32) :
    Result (ControlFlow (List U8 × List U32) FieldState13) := do
  let (item,rest) := field_next14 state.2
  match item with
  | none => .ok (.done (.Ok (),state.1))
  | some value =>
    if value ≥ 2147483647#u32 then .ok (.done (.Err .Public,state.1))
    else do
      let out ← append state.1 value
      .ok (.cont (out,rest))

def fields_source14 (append : AppendWord13) (out : List U8) (values : List U32) :
    Result FieldState13 := loop (fields_body14 append) (out,values)

theorem fields_iterator_binding14 (append : AppendWord13) (out : List U8) (values : List U32) :
    fields_source14 append out values = fields_model13 append out values := by
  unfold fields_source14
  induction values generalizing out with
  | nil => rw [loop.eq_1]; rfl
  | cons value rest ih =>
    rw [loop.eq_1]
    simp only [fields_body14,field_next14,fields_model13]
    split
    · rfl
    · cases h : append out value with
      | fail e => rfl
      | div => rfl
      | ok next => simpa only [bind_tc_ok] using ih next

theorem fields_source_link14 (append : AppendWord13) : PV_B3P_Link_fields append (fields_source14 append) :=
  funext fun out => funext (fields_iterator_binding14 append out)
#print axioms fields_iterator_binding14
#print axioms fields_source_link14
end PV_B3P_Fields14227
