import PV_B3P_Ordered227
import PV_B3P_NativeFieldsVec226
import PV_B3P_FieldsModel13227
namespace PV_B3P_Fields15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 Result
set_option autoImplicit false

abbrev Bytes15 := alloc.vec.Vec U8

def append_bytes15 (out : List U8) (value : U32) : Result (List U8) :=
  if out.length + 4 ≤ Usize.max then
    .ok (out ++ PV_B3P_ByteLayout226V3.wordBytes value)
  else .fail Error.panic

def append_vec15 (out : Bytes15) (value : U32) : Result Bytes15 :=
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (PV_B3P_NativeFieldsVec226.wordSlice value)

theorem append_vec_projection15 (out : Bytes15) (value : U32) :
    (do let next ← append_vec15 out value; .ok next.val) = append_bytes15 out.val value := by
  have width : (PV_B3P_NativeFieldsVec226.wordSlice value).val.length = 4 := by
    rw [PV_B3P_NativeFieldsVec226.word_slice_value]
    rfl
  by_cases capacity : out.val.length + 4 ≤ Usize.max
  · obtain ⟨next,extended,contents⟩ := PV_B3P_VecValue226.u8_extend out
      (PV_B3P_NativeFieldsVec226.wordSlice value) (by rwa [width])
    simp only [append_vec15,extended,bind_tc_ok,append_bytes15,capacity,if_true,contents,
      PV_B3P_NativeFieldsVec226.word_slice_value]
  · have failed := PV_B3P_VecValue226.extend_failure out
      (PV_B3P_NativeFieldsVec226.wordSlice value) (by rwa [width])
    simp only [append_vec15,failed,bind_tc_fail,append_bytes15,capacity,if_false]
#print axioms append_vec_projection15
end PV_B3P_Fields15227
