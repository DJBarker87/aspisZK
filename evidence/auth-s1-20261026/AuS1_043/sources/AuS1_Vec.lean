import AuS1_Row30
import AuS1_Block
import AuS1_Frame
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Vec
open Aeneas Aeneas.Std Result

 theorem list_clone (xs : List U8) :
    List.clone core.clone.CloneU8.clone xs = ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.clone,core.clone.CloneU8,core.clone.impls.CloneU8.clone,
      liftFun1,bind_tc_ok,ih]

 theorem slice_clone (s : Slice U8) : Slice.clone core.clone.CloneU8.clone s = ok s := by
  unfold Slice.clone
  rw [list_clone]
  rfl

 theorem extend (v out : alloc.vec.Vec U8) (s : Slice U8)
    (success : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok out) :
    out.val = v.val ++ s.val := by
  unfold alloc.vec.Vec.extend_from_slice at success
  split at success
  · rw [slice_clone] at success
    exact (congrArg Subtype.val (Result.ok.inj success)).symm
  · cases success

 theorem payload (root : Array U8 32#usize) (tail : Slice U8) (bytes1 bytes2 : alloc.vec.Vec U8)
    (first : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 256#usize) root.to_slice = ok bytes1)
    (second : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 tail = ok bytes2) :
    bytes2.deref.val = root.val ++ tail.val := by
  rw [show bytes2.deref.val = bytes2.val from rfl,extend _ _ _ second,extend _ _ _ first]
  rfl

#print axioms list_clone
#print axioms slice_clone
#print axioms extend
#print axioms payload
end AspisR1.AuS1_Vec
end
