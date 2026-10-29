import PV_B3P_Ordered227
import PV_B3P_EndianVerified226V3
import PV_B3P_VecValue226
import PV_B3P_FieldsModel13227
namespace PV_B3P_Fields15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 Result
set_option autoImplicit false

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
