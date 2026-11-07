import NMT_345EqByte
set_option autoImplicit false
namespace NMT_R2_StdByte
open Aeneas Aeneas.Std

theorem native (x y : U8) : core.cmp.PartialEqU8.eq x y = .ok (decide (x = y)) := by
 first
 | rfl
 | simp [core.cmp.PartialEqU8,liftFun2,core.cmp.impls.PartialEqU8.eq]
#print axioms native
end NMT_R2_StdByte
