import PoolS2_RightExact
set_option autoImplicit false
namespace AspisR1.PoolS2_UniqueStep
open Aeneas Aeneas.Std Result ControlFlow PoolS2_RightStep

theorem step (keys : Slice Key) (left : Usize) (within : left.val < keys.val.length) :
    PoolS2_Unique.unique_keys_loop.body keys left true =
      ok (cont (Usize.wrapping_add left 1#usize,
        (keys.val.drop (left.val+1)).all
          (fun other => decide ((keys.val[left.val]).val ≠ other.val)))) := by
  have more : left < Slice.len keys := by scalar_tac
  simp [PoolS2_Unique.unique_keys_loop.body,more,PoolS2_RightExact.exact keys left within,lift]

theorem stopped (keys : Slice Key) (left : Usize) :
    PoolS2_Unique.unique_keys_loop.body keys left false = ok (done false) := by
  simp [PoolS2_Unique.unique_keys_loop.body]

theorem ended (keys : Slice Key) (left : Usize) (unique : Bool)
    (outside : ¬ left < Slice.len keys) :
    PoolS2_Unique.unique_keys_loop.body keys left unique = ok (done unique) := by
  simp [PoolS2_Unique.unique_keys_loop.body,outside]

#print axioms step
#print axioms stopped
#print axioms ended
end AspisR1.PoolS2_UniqueStep
