import PV_B3P_ImmutableCursor14227
import PV_B3P_FieldsIterator14227
namespace PV_B3P_Fields14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 PV_B3P_Loans14227 Result ControlFlow
set_option autoImplicit false

def cursor_fields_body14 (append : AppendWord13)
    (state : List U8 × ImmutableCursor14 U32) :
    Result (ControlFlow (List U8 × ImmutableCursor14 U32) FieldState13) := do
  let (item,cursor) := cursor_next14 state.2
  match item with
  | none => .ok (.done (.Ok (),state.1))
  | some loan =>
    let value := loan.value
    if value ≥ 2147483647#u32 then .ok (.done (.Err .Public,state.1))
    else do
      let out ← append state.1 value
      .ok (.cont (out,cursor))

theorem cursor_fields_body_cons14 (append : AppendWord13) (out : List U8)
    (region : Nat) (prefix : List U32) (value : U32) (rest : List U32) :
    cursor_fields_body14 append (out,⟨region,prefix,value::rest⟩) =
      (if value ≥ 2147483647#u32 then .ok (.done (.Err .Public,out))
       else do let next ← append out value; .ok (.cont (next,⟨region,prefix++[value],rest⟩))) := rfl


def cursor_fields14 (append : AppendWord13) (out : List U8) (cursor : ImmutableCursor14 U32) :
    Result FieldState13 := loop (cursor_fields_body14 append) (out,cursor)

theorem cursor_fields_binding14 (append : AppendWord13) (out : List U8)
    (region : Nat) (prefix values : List U32) :
    cursor_fields14 append out ⟨region,prefix,values⟩ = fields_model13 append out values := by
  unfold cursor_fields14
  induction values generalizing out prefix with
  | nil => rw [loop.eq_1]; rfl
  | cons value rest ih =>
    rw [loop.eq_1,cursor_fields_body_cons14]
    rw [fields_model13]
    by_cases bad : value ≥ 2147483647#u32
    · simp only [bad,if_true]
    · simp only [bad,if_false]
      cases h : append out value with
      | fail e => rfl
      | div => rfl
      | ok next => simpa only [bind_tc_ok] using ih next (prefix++[value])

theorem fields_slice_caller14 (append : AppendWord13) (out : List U8)
    (region : Nat) (values : List U32) :
    cursor_fields14 append out (cursor_new14 region values) = fields_source14 append out values :=
  Eq.trans (cursor_fields_binding14 append out region [] values)
    (fields_iterator_binding14 append out values).symm
#print axioms cursor_fields_body_cons14
#print axioms cursor_fields_binding14
#print axioms fields_slice_caller14
end PV_B3P_Fields14227
