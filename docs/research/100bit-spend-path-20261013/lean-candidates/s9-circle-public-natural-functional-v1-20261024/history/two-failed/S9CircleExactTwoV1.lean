import AspisV8R15.ExactTowerBase
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace AspisR1S9CircleExactTwoV1
open AspisV8R15.ExactTowerBase

/-- The actual quartic field has nonzero2, via the two existing injective
base-field algebra maps; no characteristic or nonzero premise is supplied. -/
theorem exact_q_two_ne_zero : (2 : QM31Exact)≠0 := by
  have hb : (2 : M31Exact)≠0 := by
    change (2 : ZMod 2147483647)≠0
    norm_num
  let f : M31Exact →+* QM31Exact :=
    (algebraMap CM31Exact QM31Exact).comp (algebraMap M31Exact CM31Exact)
  intro hq
  apply hb
  apply f.injective
  calc
    f (2 : M31Exact)=(2 : QM31Exact) := map_ofNat f 2
    _ = 0 := hq
    _ = f 0 := (map_zero f).symm

#print axioms exact_q_two_ne_zero
end AspisR1S9CircleExactTwoV1
