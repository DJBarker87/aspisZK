import NDF_RawValue
import NDF_RawBridge
import KMX_CopyMeaning
set_option autoImplicit false
namespace NDI_RawProjection
open Aeneas Aeneas.Std Result

theorem byte (N : Usize) (bytes : Slice U8) (offset : Usize)
    (fit : offset.val+N.val≤bytes.val.length) :
    ∃ out finish, NDF_ReaderRef.raw_ref N bytes offset=ok (out,finish) ∧
      (∀ j, j<N.val → out.val[j]?=bytes.val[offset.val+j]?) ∧
      finish.val=offset.val+N.val := by
  obtain ⟨out,finish,call,contents,cursor⟩ := NDF_RawValue.total N bytes offset fit
  refine ⟨out,finish,call,?_,cursor⟩
  intro j bound
  rw [contents,List.getElem?_take,if_pos bound,List.getElem?_drop]

theorem kmx_window {α : Type} (bytes initial : Nat → α) (offset start count j : Nat) :
    KMX_CopyMeaning.loop (fun k => bytes (offset+k)) initial start count j =
      if start≤j ∧ j<start+count then bytes (offset+j) else initial j :=
  KMX_CopyMeaning.loop_spec _ _ _ _ _

theorem kmx_disjoint {α : Type} (bytes initial : Nat → α) (offset start count j : Nat)
    (outside : j<start ∨ start+count≤j) :
    KMX_CopyMeaning.loop (fun k => bytes (offset+k)) initial start count j = initial j :=
  KMX_CopyMeaning.copy_frame _ _ _ _ _ outside

#print axioms byte
#print axioms kmx_window
#print axioms kmx_disjoint
end NDI_RawProjection
