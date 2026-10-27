import PoolS2_UniqueLoop
set_option autoImplicit false
namespace AspisR1.PoolS2_UniqueExact
open Aeneas Aeneas.Std Result PoolS2_RightStep PoolS2_UniqueSuffix

theorem exact (keys : Slice Key) :
    PoolS2_Unique.unique_keys keys = ok (decide (allDifferent keys.val)) := by
  simpa [PoolS2_Unique.unique_keys,remaining] using
    PoolS2_UniqueLoop.exact keys 0#usize true (by simp)

theorem accepted (keys : Slice Key) :
    PoolS2_Unique.unique_keys keys = ok true ↔ allDifferent keys.val := by
  rw [exact]
  simp

theorem rejected (keys : Slice Key) :
    PoolS2_Unique.unique_keys keys = ok false ↔ ¬ allDifferent keys.val := by
  rw [exact]
  simp

#print axioms exact
#print axioms accepted
#print axioms rejected
end AspisR1.PoolS2_UniqueExact
