import RPv_FIy_IteratorTraversal
set_option autoImplicit false
namespace AspisR1.FIy_Writeback
open Aeneas Aeneas.Std Result FIq_Native
open FIy_IteratorTraversal

theorem length (v : Nat → QM) (s n : Nat) (im : IterMut) :
    (deferredWrites v s n im).slice.val.length=im.slice.val.length := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [deferredWrites,Slice.setAtNat,List.length_set] using ih (s+1)

theorem index (v : Nat → QM) (s n : Nat) (im : IterMut) :
    (deferredWrites v s n im).i=im.i := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (s+1)

#check List.getElem?_set
#check List.getElem?_set_self
#check List.getElem?_set_ne
#check List.getElem?_mapIdx
#check List.ext_getElem?
#print Aeneas.Std.Slice.setAtNat
#print axioms length
#print axioms index
end AspisR1.FIy_Writeback
