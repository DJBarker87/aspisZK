/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.SelectedArithmetic

/-- Arithmetic constants from the audited selected research profile. -/
def p : ℕ := 2147483647
def fieldSize : ℕ := p^4
def circleDomain : ℕ := fieldSize-p^2
def productDegree : ℕ := 90407376

def pairCeiling : ℚ :=
  (productDegree:ℚ)*(productDegree-1:Nat)/((circleDomain:ℚ)*(circleDomain-1:Nat))

/-- Conservative decimal rational ceiling for the REPORTED conditional
residual. A bridge to integratedBudget is intentionally not asserted. -/
def reportedResidualCeiling : ℚ := 493081653/(10:ℚ)^40

theorem pair_under_195 : pairCeiling < 1/(2:ℚ)^195 := by
  norm_num [pairCeiling, productDegree, circleDomain, fieldSize, p]

theorem residual_under_103 : reportedResidualCeiling < 1/(2:ℚ)^103 := by
  norm_num [reportedResidualCeiling]

theorem residual_over_104 : 1/(2:ℚ)^104 < reportedResidualCeiling := by
  norm_num [reportedResidualCeiling]

/-- Diagnostic: a 16-attempt union of THIS ceiling does not certify 100 bits.
This is not a lower bound on attack probability, nor an attack construction. -/
theorem sixteen_union_over_100 : 1/(2:ℚ)^100 < 16*reportedResidualCeiling := by
  norm_num [reportedResidualCeiling]

#print axioms pair_under_195
#print axioms residual_under_103
#print axioms sixteen_union_over_100
end AspisV8Completion.SelectedArithmetic
