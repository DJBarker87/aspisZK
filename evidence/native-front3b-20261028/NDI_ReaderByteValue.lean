import NDI_ReaderByteRef.Funs
set_option autoImplicit false
namespace NDI_ReaderByteValue
open Aeneas Aeneas.Std Result

theorem total (bytes : Slice U8) (offset width coordinate : Usize)
    (fit : offset.val+width.val≤bytes.val.length) (bound : coordinate.val<width.val) :
    ∃ value finish, NDI_ReaderByteRef.raw_byte_ref bytes offset width coordinate=ok (value,finish) ∧
      bytes.val[offset.val+coordinate.val]?=some value ∧ finish.val=offset.val+width.val := by
  have cap := bytes.property
  obtain ⟨address,add,addressVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=offset) (y:=coordinate) (by omega))
  obtain ⟨value,read,contents⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec bytes address (by change address.val<bytes.val.length;omega))
  obtain ⟨finish,advance,finishVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=offset) (y:=width) (by omega))
  refine ⟨value,finish,?_,?_,finishVal⟩
  · simp only [NDI_ReaderByteRef.raw_byte_ref,add,read,advance,bind_tc_ok]
  · rw [List.getElem?_eq_getElem (by omega : offset.val+coordinate.val<bytes.val.length)]
    congr 1
    simpa only [addressVal] using contents.symm

#print axioms total
end NDI_ReaderByteValue
