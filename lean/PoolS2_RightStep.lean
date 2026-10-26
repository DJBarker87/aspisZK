import PoolS2_KeyExact
set_option autoImplicit false
namespace AspisR1.PoolS2_RightStep
open Aeneas Aeneas.Std Result ControlFlow
abbrev Key := Array U8 32#usize

theorem step (keys : Slice Key) (left right : Usize) (a b : Key)
    (within : right < Slice.len keys)
    (ra : Slice.index_usize keys left = ok a) (rb : Slice.index_usize keys right = ok b) :
    PoolS2_Unique.right_unique_loop.body keys left right true =
      ok (cont (Usize.wrapping_add right 1#usize, decide (a.val ≠ b.val))) := by
  simp [PoolS2_Unique.right_unique_loop.body,within,ra,rb,lift,
    PoolS2_KeyExact.exact,Array.to_slice]

theorem stopped (keys : Slice Key) (left right : Usize) :
    PoolS2_Unique.right_unique_loop.body keys left right false = ok (done false) := by
  simp [PoolS2_Unique.right_unique_loop.body]

theorem ended (keys : Slice Key) (left right : Usize) (unique : Bool)
    (outside : ¬ right < Slice.len keys) :
    PoolS2_Unique.right_unique_loop.body keys left right unique = ok (done unique) := by
  simp [PoolS2_Unique.right_unique_loop.body,outside]

#print axioms step
#print axioms stopped
#print axioms ended
end AspisR1.PoolS2_RightStep
