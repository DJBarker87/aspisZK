"""Bind the fields caller to Vec operations while retaining partial error state.
This is caller composition, not pv-b3q's std implementation catalogue.
"""
from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');files={}
h='''namespace PV_B3P_Fields15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
files['PV_B3P_FieldsVecPort15227']='import PV_B3P_Ordered227\nimport PV_B3P_EndianVerified226V3\nimport PV_B3P_VecValue226\nimport PV_B3P_FieldsModel13227\n'+h+'''
abbrev Bytes15 := alloc.vec.Vec U8

def word_slice15 (value : U32) : Slice U8 :=
  ⟨(core.num.U32.to_le_bytes value).val, by
    rw [←PV_B3P_EndianVerified226V3.word_bytes]
    change 4 ≤ Usize.max
    scalar_tac⟩

theorem word_slice_value15 (value : U32) :
    (word_slice15 value).val = PV_B3P_ByteLayout226V3.wordBytes value :=
  (PV_B3P_EndianVerified226V3.word_bytes value).symm
#print axioms word_slice_value15

def append_bytes15 (out : List U8) (value : U32) : Result (List U8) :=
  if out.length + 4 ≤ Usize.max then
    .ok (out ++ PV_B3P_ByteLayout226V3.wordBytes value)
  else .fail Error.panic

def append_vec15 (out : Bytes15) (value : U32) : Result Bytes15 :=
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (word_slice15 value)

theorem append_vec_projection15 (out : Bytes15) (value : U32) :
    (do let next ← append_vec15 out value; .ok next.val) = append_bytes15 out.val value := by
  have width : (word_slice15 value).val.length = 4 := by
    rw [word_slice_value15]
    rfl
  by_cases capacity : out.val.length + 4 ≤ Usize.max
  · obtain ⟨next,extended,contents⟩ := PV_B3P_VecValue226.u8_extend out
      (word_slice15 value) (by rwa [width])
    simp only [append_vec15,extended,bind_tc_ok,append_bytes15,capacity,if_true,contents,
      word_slice_value15]
  · have failed := PV_B3P_VecValue226.extend_failure out
      (word_slice15 value) (by rwa [width])
    simp only [append_vec15,failed,bind_tc_fail,append_bytes15,capacity,if_false]
#print axioms append_vec_projection15
end PV_B3P_Fields15227
'''
files['PV_B3P_FieldsVecState15227']='import PV_B3P_FieldsVecPort15227\n'+h+'''
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
'''
files['PV_B3P_FieldsVecCaller15227']='import PV_B3P_FieldsVecState15227\nimport PV_B3P_FieldsCursor14227\n'+h+'''
/-- The source caller's full Result retains the Vec on Rust Err, including
all successful earlier appends. The cursor carries the immutable input loan. -/
theorem fields_vec_cursor_projection15 (out : Bytes15) (values : List U32)
    (region : Nat) :
    (do let state ← fields_vec15 out values; .ok (erase_vec_state15 state)) =
      PV_B3P_Fields14227.cursor_fields14 append_bytes15 out.val
        (PV_B3P_Loans14227.cursor_new14 region values) := by
  rw [fields_vec_projection15]
  exact (PV_B3P_Fields14227.cursor_fields_binding14 append_bytes15 out.val region [] values).symm

/-- Honest explicit model witness uses the same append for every source step;
this does not assert infallible native allocation or instantiate the catalogue. -/
theorem fields_vec_joint_witness15 :
    PV_B3P_Link_fields append_bytes15 (PV_B3P_Fields14227.fields_source14 append_bytes15) :=
  PV_B3P_Fields14227.fields_source_link14 append_bytes15
#print axioms fields_vec_cursor_projection15
#print axioms fields_vec_joint_witness15
end PV_B3P_Fields15227
'''
for m,s in files.items():(L/(m+'.lean')).write_text(s)
print(' '.join(files))
