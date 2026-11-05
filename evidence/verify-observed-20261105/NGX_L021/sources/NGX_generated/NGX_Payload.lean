import NGX_StateImpl
import NFU_PrefixRecords
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NGX_Payload

def computation (reply : Result (core.result.Result (Slice U8) r1_wire.Error)) :
 Result (core.result.Result (Slice U8) r1_wire.Error) := do
 let r ← reply
 match r with
 | .Err error => ok (.Err error)
 | .Ok framed => do
   let payload ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) framed {start:=5#usize}
   ok (.Ok payload)

theorem source (prefix1 : r1_wire.Prefix) (row : U8) :
 FinishModel.payload prefix1 row=computation (NFU_PrefixRecords.selected prefix1 row) := by
 rw [← NFU_PrefixRecords.record]
 unfold FinishModel.payload computation
 cases h : r1_wire.Prefix.record prefix1 row <;> simp only [h,bind_tc_fail,bind_tc_div,bind_tc_ok]
 rename_i r
 cases r <;> rfl

theorem rejected (error : r1_wire.Error) : computation (ok (.Err error))=ok (.Err error) := by rfl

/-- Actual selected borrowed slice is passed to the tail operation. The
full source Result, including a bad index failure outside the parser domain,
is preserved rather than silently replacing it by successful bytes. -/
theorem selected (framed : Slice U8) :
 computation (ok (.Ok framed)) = do
  let payload ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) framed {start:=5#usize}
  ok (.Ok payload) := by rfl
#print axioms source
#print axioms rejected
#print axioms selected
end AspisR1.NGX_Payload

namespace AspisR1.NGX_Payload
 theorem tail_total (framed : Slice U8) (enough : 5≤framed.val.length) :
 ∃ payload, computation (ok (.Ok framed))=ok (.Ok payload) ∧
   payload.val=framed.val.drop 5 ∧ payload.val.length=framed.val.length-5 := by
 rw [selected]
 simp only [Slice.index_SliceIndexRangeFromUsizeSliceInst]
 unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index
 split
 · refine ⟨_,rfl,rfl,?_⟩
   simp only [List.length_drop]
 · rename_i outside
   exfalso
   apply outside
   simpa using enough
#print axioms tail_total
end AspisR1.NGX_Payload
