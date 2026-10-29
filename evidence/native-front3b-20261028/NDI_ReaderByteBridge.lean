import NDI_ReaderByteValue
import NDI_RawProjection
set_option autoImplicit false
namespace NDI_ReaderByteBridge
open Aeneas Aeneas.Std Result

theorem reference (width : Usize) (bytes : Slice U8) (offset coordinate : Usize)
    (fit : offset.val+width.val≤bytes.val.length) (bound : coordinate.val<width.val) :
    ∃ out finish value, NDF_ReaderRef.raw_ref width bytes offset=ok (out,finish) ∧
      NDI_ReaderByteRef.raw_byte_ref bytes offset width coordinate=ok (value,finish) ∧
      out.val[coordinate.val]?=some value := by
  obtain ⟨out,finish,call,cells,advance⟩ := NDI_RawProjection.byte width bytes offset fit
  obtain ⟨value,finish',byte,cell,advance'⟩ := NDI_ReaderByteValue.total bytes offset width coordinate fit bound
  have same : finish'=finish := UScalar.eq_of_val_eq (advance'.trans advance.symm)
  subst finish'
  exact ⟨out,finish,value,call,byte,(cells coordinate.val bound).trans cell⟩

#print axioms reference
end NDI_ReaderByteBridge
