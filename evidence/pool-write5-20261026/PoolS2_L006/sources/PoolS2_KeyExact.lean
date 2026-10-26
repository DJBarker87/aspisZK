import PoolS2_KeyLoop
set_option autoImplicit false
namespace AspisR1.PoolS2_KeyExact
open Aeneas Aeneas.Std Result PoolS2_KeySuffix

theorem zip_equal (a b : List U8) (length : a.length = b.length) :
    (a.zip b).all (fun p => decide (p.1 = p.2)) = decide (a = b) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp_all
    | cons y ys =>
      have tail : xs.length = ys.length := by simpa using length
      simp [List.zip_cons_cons,ih ys tail]

theorem exact (a b : Slice U8) :
    PoolS2_Unique.key_equal a b = ok (decide (a.val = b.val)) := by
  by_cases same : a.val.length = b.val.length
  · have sizes : Slice.len a = Slice.len b := by scalar_tac
    simp only [PoolS2_Unique.key_equal,sizes,bne_self_eq_false,if_false]
    rw [PoolS2_KeyLoop.exact a b 0#usize true same (by simp)]
    simp [remaining,pairs,zip_equal a.val b.val same]
  · have sizes : Slice.len a ≠ Slice.len b := by scalar_tac
    have different : a.val ≠ b.val := fun h => same (congrArg List.length h)
    simp [PoolS2_Unique.key_equal,sizes,different]

#print axioms zip_equal
#print axioms exact
end AspisR1.PoolS2_KeyExact
