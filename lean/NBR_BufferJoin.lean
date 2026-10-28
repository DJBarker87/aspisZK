import NBR_ProducerBuffers
import NBR_RangeJoin
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
  refine ⟨by simp only [logical,List.length_append,semSize,ySize],?_,?_⟩
  · exact NBR_RangeJoin.first semantic y1 (logical semantic y1 semSize ySize) 13831#usize rfl semSize.symm
  · exact NBR_RangeJoin.suffix semantic y1 (logical semantic y1 semSize ySize)
      13831#usize 14759#usize rfl semSize.symm (by rw [ySize];scalar_tac)

#print axioms source
end AspisR1.NBR_BufferJoin
