import NDO_JGn_ActiveData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_ActiveMath
open FIv_NativeValue (decode)
open JGn_ActiveData
theorem chunk0 : block0.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a00)=
    decode a08 := by
  jgl_words
#print axioms chunk0
theorem chunk1 : block1.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a08)=
    decode a16 := by
  jgl_words
#print axioms chunk1
theorem chunk2 : block2.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a16)=
    decode a24 := by
  jgl_words
#print axioms chunk2
theorem chunk3 : block3.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a24)=
    decode a32 := by
  jgl_words
#print axioms chunk3
theorem chunk4 : block4.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a32)=
    decode a40 := by
  jgl_words
#print axioms chunk4
theorem chunk5 : block5.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a40)=
    decode a48 := by
  jgl_words
#print axioms chunk5
theorem chunk6 : block6.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a48)=
    decode a56 := by
  jgl_words
#print axioms chunk6
theorem chunk7 : block7.foldl (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a56)=
    decode a64 := by
  jgl_words
#print axioms chunk7
attribute [local irreducible] List.foldl FJk_ActiveValue.step
theorem value : FJk_ActiveValue.model JGl_NumericData.selectors 0 0=decode a64 := by
  have layout : FJk_ActiveValue.indices=block0++block1++block2++block3++block4++block5++block6++block7 := by rfl
  unfold FJk_ActiveValue.model
  rw [List.drop_zero,layout]
  change ((block0++block1++block2++block3++block4++block5++block6++block7).foldl
    (FJk_ActiveValue.step JGl_NumericData.selectors) (decode a00))=decode a64
  simp only [List.foldl_append]
  rw [chunk0,chunk1,chunk2,chunk3,chunk4,chunk5,chunk6,chunk7]
#print axioms value
end AspisR1.JGn_ActiveMath
end
