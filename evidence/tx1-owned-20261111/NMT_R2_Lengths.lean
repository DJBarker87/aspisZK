import NMT_345RSLCarriers
set_option autoImplicit false
namespace NMT_R2_Lengths
open Aeneas Aeneas.Std

theorem slice {A : Type} (bytes : Slice A) : (Slice.len bytes).val = bytes.val.length := by
 simp [Slice.len]

theorem vec {A : Type} (bytes : alloc.vec.Vec A) : (alloc.vec.Vec.len bytes).val = bytes.val.length := by
 simp [alloc.vec.Vec.len,Slice.len]
#print axioms slice
#print axioms vec
end NMT_R2_Lengths
