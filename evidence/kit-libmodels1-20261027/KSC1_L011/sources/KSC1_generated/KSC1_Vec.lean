import KSA_XRn_Join_FunsExternal
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1

theorem vec_is_empty {T : Type} (allocator : Type) (v : alloc.vec.Vec T) :
    KSA_Isolated.alloc.vec.Vec.is_empty allocator v = ok (decide (v.val.length = 0)) := by
  cases h : v.val <;> simp [KSA_Isolated.alloc.vec.Vec.is_empty, h]

#print axioms vec_is_empty
end KSC1
