import KSA_XRn_Join_ABI
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1.P7

theorem slice_array_eq {T U : Type} {N : Usize}
    (cmp : core.cmp.PartialEq T U) (s : Slice T) (a : Array U N) :
    KSA_Isolated.Slice.Insts.CoreCmpPartialEqArray.eq cmp s a =
      core.slice.cmp.PartialEqSlice.eq cmp s a.to_slice := rfl

theorem slice_array_ne {T U : Type} {N : Usize}
    (cmp : core.cmp.PartialEq T U) (s : Slice T) (a : Array U N) :
    KSA_Isolated.Slice.Insts.CoreCmpPartialEqArray.ne cmp s a =
      core.slice.cmp.PartialEqSlice.ne cmp s a.to_slice := rfl

theorem next_projection {T : Type} (s : core.slice.iter.IterMut T) :
    KSA_Isolated.XRn_Join_next s =
      (do let (v,t,_) ← core.slice.iter.IteratorIterMut.next s; ok (v,t)) := rfl

-- Conversion law is deliberately guarded by the exact full-array length.
theorem restored_array {T : Type} {N : Usize} (a : Array T N) (s : Slice T)
    (h : s.val.length = N.val) : (Array.from_slice a s).val = s.val :=
  Array.from_slice_val a s h

#print axioms slice_array_eq
#print axioms slice_array_ne
#print axioms next_projection
#print axioms restored_array
#print core.slice.iter.IteratorIterMut.next
#print core.slice.cmp.PartialEqSlice.eq
#print core.slice.cmp.PartialEqSlice.ne
#print Array.from_slice
end KSC1.P7
