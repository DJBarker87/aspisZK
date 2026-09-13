import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Generic graph algebra. Matching source tuple values and the pole-free
branch are supplied by the honest-source adapter. -/
set_option autoImplicit false
namespace AspisV8H1C2
noncomputable section
variable {E R K : Type*} [Fintype E] [DecidableEq R] [Field K]

def incidence (src dst : E → R) (a : E → K) (r : R) : K :=
  ∑ e, ((if src e = r then a e else 0) - (if dst e = r then a e else 0))

theorem incidence_add (src dst : E → R) (a b : E → K) :
    incidence src dst (a + b) = incidence src dst a + incidence src dst b := by
  funext r
  simp only [incidence, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem incidence_smul (src dst : E → R) (c : K) (a : E → K) :
    incidence src dst (c • a) = c • incidence src dst a := by
  classical
  funext r
  simp only [incidence, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ e, ((if src e = r then c * a e else 0) -
        (if dst e = r then c * a e else 0)) =
        ∑ e, c * ((if src e = r then a e else 0) -
          (if dst e = r then a e else 0)) := by
            apply Finset.sum_congr rfl
            intro e _
            split_ifs <;> ring
    _ = c * ∑ e, ((if src e = r then a e else 0) -
        (if dst e = r then a e else 0)) := by
          symm
          exact map_sum (AddMonoidHom.mulLeft c) _ _

def incidenceMap (src dst : E → R) : (E → K) →ₗ[K] (R → K) where
  toFun := incidence src dst
  map_add' := incidence_add src dst
  map_smul' := incidence_smul src dst

def coeff (weight : K) (chi phi : K) : K := by
  classical
  exact if weight = 0 then 0 else weight / (chi - phi)

def helperByRows (src dst : E → R) (weight prod cons : E → K) (chi : K) (r : R) : K :=
  ∑ e, ((if src e = r then coeff (weight e) chi (prod e) else 0) -
    (if dst e = r then coeff (weight e) chi (cons e) else 0))

def PoleFree (weight prod cons : E → K) (chi : K) : Prop :=
  ∀ e, weight e ≠ 0 → chi ≠ prod e ∧ chi ≠ cons e

/-- Rational witness dependence is confined to the edge coefficients. -/
theorem helper_eq_incidence (src dst : E → R) (weight prod cons : E → K)
    (chi : K) (matching : ∀ e, weight e ≠ 0 → prod e = cons e) :
    helperByRows src dst weight prod cons chi =
      incidence src dst (fun e => coeff (weight e) chi (prod e)) := by
  classical
  funext r
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : weight e = 0
  · simp [coeff, h]
  · simp [matching e h]

/-- This checked model retains singular failures. It is not definitionally Rust. -/
def checkedHelper (src dst : E → R) (weight prod cons : E → K) (chi : K) :
    Option (R → K) := by
  classical
  exact if PoleFree weight prod cons chi then
    some (helperByRows src dst weight prod cons chi) else none

theorem checkedHelper_success_is_pole_free (src dst : E → R)
    (weight prod cons : E → K) (chi : K) (out : R → K)
    (success : checkedHelper src dst weight prod cons chi = some out) :
    PoleFree weight prod cons chi := by
  classical
  unfold checkedHelper at success
  split_ifs at success with h
  · exact h

#print axioms helper_eq_incidence
#print axioms checkedHelper_success_is_pole_free
end
end AspisV8H1C2
