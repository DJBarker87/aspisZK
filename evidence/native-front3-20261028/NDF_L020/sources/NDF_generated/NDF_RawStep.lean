import NDF_ReaderRef.Funs
import NDF_CheckedWrapping
set_option autoImplicit false
namespace NDF_RawStep
open Aeneas Aeneas.Std Result ControlFlow

theorem step {N : Usize} (bytes : Slice U8) (offset j : Usize) (out : Array U8 N)
    (fit : offset.val+N.val ≤ bytes.val.length) (active : j.val<N.val) :
    ∃ (next : Usize) (value : U8), next.val=j.val+1 ∧
      bytes.val[offset.val+j.val]?=some value ∧
      NDF_ReaderRef.raw_ref_loop.body bytes offset out j=ok (cont (out.set j value,next)) := by
  have max := bytes.property
  obtain ⟨address,add,addressVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=offset) (y:=j) (by omega))
  obtain ⟨value,read,valueEq⟩ := WP.spec_imp_exists
    (Slice.index_usize_spec bytes address (by change address.val<bytes.val.length; omega))
  obtain ⟨changed,write,changedEq⟩ := WP.spec_imp_exists
    (Array.update_spec out j value (by have := out.property; scalar_tac))
  obtain ⟨next,inc,nextVal⟩ := WP.spec_imp_exists
    (Usize.add_spec (x:=j) (y:=1#usize) (by scalar_tac))
  refine ⟨next,value,nextVal,?_,?_⟩
  · rw [List.getElem?_eq_getElem (by omega : offset.val+j.val<bytes.val.length)]
    congr 1
    simpa only [addressVal] using valueEq.symm
  · have h : j<N := active
    simp only [NDF_ReaderRef.raw_ref_loop.body,if_pos h,add,read,write,inc,bind_tc_ok,changedEq]

theorem done_step {N : Usize} (bytes : Slice U8) (offset j : Usize) (out : Array U8 N)
    (terminal : N.val≤j.val) :
    NDF_ReaderRef.raw_ref_loop.body bytes offset out j=ok (done out) := by
  have h : ¬j<N := by scalar_tac
  simp only [NDF_ReaderRef.raw_ref_loop.body,if_neg h]

#print axioms step
#print axioms done_step
end NDF_RawStep
