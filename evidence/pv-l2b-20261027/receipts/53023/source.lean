import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace PV_L2B_SamplerLaw
-- IID path weights, not an axiom identifying SHA outputs with IID words.
def geom (q : ℚ) (r : Nat) : ℚ := q^r * (1-q)
def success (q : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => (1-q)+q*success q n
def valueMass (q u : ℚ) : Nat → ℚ
  | 0 => 0
  | n+1 => u+q*valueMass q u n
def prefixMass (q u : ℚ) (r : Nat) : ℚ := q^r*u
theorem geometric_zero (q : ℚ) : geom q 0 = 1-q := by simp [geom]
#print axioms geometric_zero
theorem geometric_step (q : ℚ) (r : Nat) : geom q (r+1) = q*geom q r := by simp [geom,pow_succ]; ring
#print axioms geometric_step
theorem success_zero (q : ℚ) : success q 0 = 0 := rfl
#print axioms success_zero
end PV_L2B_SamplerLaw
