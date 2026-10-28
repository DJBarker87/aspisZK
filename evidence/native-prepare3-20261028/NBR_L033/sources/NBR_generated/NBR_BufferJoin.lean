import NBR_ProducerBuffers
set_option autoImplicit false
namespace AspisR1.NBR_BufferJoin
open Aeneas Aeneas.Std Result

def logical (semantic y1 : Slice U8) (semSize : semantic.val.length=13831)
    (ySize : y1.val.length=928) : Slice U8 :=
  ⟨semantic.val++y1.val,by simp only [List.length_append,semSize,ySize];scalar_tac⟩

/-- The final joined carrier's two native ranges are exactly the produced
buffers; this is a value/geometry theorem, not allocator ownership. -/
theorem source (semantic y1 : Slice U8) (semSize : semantic.val.length=13831)
    (ySize : y1.val.length=928) :
    (logical semantic y1 semSize ySize).val.length=14759 ∧
    NBL_SlicePort.segment (logical semantic y1 semSize ySize) 0#usize 13831#usize=semantic ∧
    NBL_SlicePort.segment (logical semantic y1 semSize ySize) 13831#usize 14759#usize=y1 := by
  refine ⟨by simp only [logical,List.length_append,semSize,ySize];omega,?_,?_⟩
  · apply Subtype.ext
    change ((semantic.val++y1.val).drop 0).take 13831=semantic.val
    rw [List.drop_zero,←semSize,List.take_left]
  · apply Subtype.ext
    change ((semantic.val++y1.val).drop (13831#usize).val).take
      ((14759#usize).val-(13831#usize).val)=y1.val
    rw [NBR_RangeGeometry.difference 13831#usize 14759#usize 928 (by scalar_tac)]
    change ((semantic.val++y1.val).drop 13831).take 928=y1.val
    rw [←semSize,List.drop_left,←ySize,List.take_length]

#print axioms source
end AspisR1.NBR_BufferJoin
