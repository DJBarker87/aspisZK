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
theorem success_closed (q : ℚ) (n : Nat) : success q n = 1-q^n := by
  induction n with
  | zero => simp [success]
  | succ n ih => rw [success, ih, pow_succ]; ring
#print axioms success_closed
theorem total_capped (q : ℚ) (n : Nat) : success q n + q^n = 1 := by rw [success_closed]; ring
#print axioms total_capped
theorem value_factor (q u : ℚ) (n : Nat) (p : ℚ) (h : u*p=1-q) : valueMass q u n * p = success q n := by
  induction n with
  | zero => simp [valueMass,success]
  | succ n ih => simp only [valueMass,success]; calc
      (u+q*valueMass q u n)*p = u*p+q*(valueMass q u n*p) := by ring
      _ = (1-q)+q*success q n := by rw [h,ih]
#print axioms value_factor
theorem uniform_on_success (q u p : ℚ) (n : Nat) (hp : p ≠ 0) (h : u*p=1-q) : valueMass q u n = success q n / p := by
  apply (eq_div_iff hp).2; exact value_factor q u n p h
#print axioms uniform_on_success
theorem prefix_independent (q u p : ℚ) (r : Nat) (h : u*p=1-q) : prefixMass q u r * p = geom q r := by
  unfold prefixMass geom; calc q^r*u*p = q^r*(u*p) := by ring
  _ = q^r*(1-q) := by rw [h]
#print axioms prefix_independent
theorem prefix_uniform (q u p : ℚ) (r : Nat) (hp : p ≠ 0) (h : u*p=1-q) : prefixMass q u r = geom q r / p := by
  apply (eq_div_iff hp).2; exact prefix_independent q u p r h
#print axioms prefix_uniform
theorem scalar_normalization (p : ℚ) (hp : p+1 ≠ 0) : (1/(p+1))*p = 1-1/(p+1) := by field_simp; ring
#print axioms scalar_normalization
theorem scalar_trace_law (p : ℚ) (hp : p+1 ≠ 0) (r : Nat) : prefixMass (1/(p+1)) (1/(p+1)) r*p = geom (1/(p+1)) r :=
  prefix_independent _ _ _ _ (scalar_normalization p hp)
#print axioms scalar_trace_law
theorem scalar_uniform (p : ℚ) (hp : p ≠ 0) (hp1 : p+1 ≠ 0) (n : Nat) : valueMass (1/(p+1)) (1/(p+1)) n = (1-(1/(p+1))^n)/p := by
  rw [uniform_on_success _ _ _ _ hp (scalar_normalization p hp1), success_closed]
#print axioms scalar_uniform
theorem scalar_prefix_product (p : ℚ) (hp : p ≠ 0) (hp1 : p+1 ≠ 0) (r : Nat) : prefixMass (1/(p+1)) (1/(p+1)) r = geom (1/(p+1)) r * (1/p) := by
  rw [prefix_uniform _ _ _ _ hp (scalar_normalization p hp1)]; ring
#print axioms scalar_prefix_product
theorem entropy_reject_partition (z : ℚ) : z + (1-z)*z = 1-(1-z)^2 := by ring
#print axioms entropy_reject_partition
theorem entropy_accept_partition (z : ℚ) : z+(1-z)*z+(1-z)^2=1 := by ring
#print axioms entropy_accept_partition
end PV_L2B_SamplerLaw
