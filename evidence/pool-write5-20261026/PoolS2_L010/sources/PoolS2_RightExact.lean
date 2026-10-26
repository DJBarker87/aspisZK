import PoolS2_RightLoop
set_option autoImplicit false
namespace AspisR1.PoolS2_RightExact
open Aeneas Aeneas.Std Result PoolS2_RightStep

theorem exact (keys : Slice Key) (left : Usize) (within : left.val < keys.val.length) :
    PoolS2_Unique.right_unique keys left = ok
      ((keys.val.drop (left.val+1)).all
        (fun other => decide ((keys.val[left.val]).val ≠ other.val))) := by
  have more : left < Slice.len keys := by scalar_tac
  have inc := PoolS2_Index.increment keys left more
  have bound : (Usize.wrapping_add left 1#usize).val ≤ keys.val.length := by rw [inc]; omega
  unfold PoolS2_Unique.right_unique
  simp only [lift,bind_tc_ok]
  rw [PoolS2_RightLoop.exact keys _ left _ true (PoolS2_Index.read keys left within) bound]
  simp [PoolS2_RightSuffix.remaining,inc]

#print axioms exact
end AspisR1.PoolS2_RightExact
