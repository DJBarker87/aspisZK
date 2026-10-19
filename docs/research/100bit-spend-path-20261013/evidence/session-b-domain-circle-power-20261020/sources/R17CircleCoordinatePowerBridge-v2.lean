import R17CircleCoordinateMulBridge

set_option autoImplicit false

namespace R17CircleCoordinatePowerBridge

open AspisCircleGroupOrder R17CircleCoordinateMulBridge

/-- The model's binary power recurrence denotes powers in the maintained
circle group after projection to coordinates. -/
theorem zPow_circleCoords (x : AspisCircleGroupOrder.C) (n : Nat) :
    R17TableBasePowerBridge.zPow (circleCoords x) n =
      circleCoords (x ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [R17TableBasePowerBridge.zPow,
        R17TableBasePowerBridge.oneZ, circleCoords]
    | succ k =>
      let m := (k + 1) / 2
      have hm : m < k + 1 := by dsimp [m]; omega
      have him := ih m hm
      have hdecomp : (k + 1) % 2 + 2 * ((k + 1) / 2) = k + 1 := by
        simpa using (Nat.mod_add_div (k + 1) 2)
      simp only [R17TableBasePowerBridge.zPow]
      by_cases hparity : (k + 1) % 2 == 0
      · have hmod : (k + 1) % 2 = 0 := of_decide_eq_true hparity
        have hn : k + 1 = m + m := by dsimp [m] at *; omega
        simp only [if_pos hparity]
        rw [him]
        calc
          R17TableBasePowerBridge.zMul (circleCoords (x ^ m))
              (circleCoords (x ^ m)) = circleCoords ((x ^ m) * (x ^ m)) :=
                zMul_circleCoords _ _
          _ = circleCoords (x ^ (k + 1)) := congrArg circleCoords (by
                rw [hn, pow_add])
      · have hmod : (k + 1) % 2 = 1 := by
          have hlt : (k + 1) % 2 < 2 := Nat.mod_lt _ (by omega)
          have hne : (k + 1) % 2 ≠ 0 := by
            intro hz
            apply hparity
            simp [hz]
          omega
        have hn : k + 1 = (m + m) + 1 := by dsimp [m] at *; omega
        simp only [if_neg hparity]
        rw [him]
        calc
          R17TableBasePowerBridge.zMul
              (R17TableBasePowerBridge.zMul (circleCoords (x ^ m))
                (circleCoords (x ^ m))) (circleCoords x) =
              R17TableBasePowerBridge.zMul
                (circleCoords ((x ^ m) * (x ^ m))) (circleCoords x) := by
                  rw [zMul_circleCoords]
          _ = circleCoords (((x ^ m) * (x ^ m)) * x) := zMul_circleCoords _ _
          _ = circleCoords (x ^ (k + 1)) := congrArg circleCoords (by
                rw [hn, pow_add, pow_add, pow_one])

#print axioms zPow_circleCoords

end R17CircleCoordinatePowerBridge
