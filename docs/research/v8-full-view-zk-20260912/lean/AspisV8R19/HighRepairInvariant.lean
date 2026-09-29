/- Query repairs confined to whole low blocks are invisible to high-supported weights. -/
import AspisV8R19.BetaUniformCorrection
import Mathlib.Data.Fintype.BigOperators

namespace AspisR19.HighRepairInvariant
open BetaUniformCorrection
variable {F : Type*} [CommRing F]
noncomputable section
abbrev Index (n : Nat) := Fin n × Fin 4

def unit {n : Nat} (d : Fin n) (s : Fin 4) (i : Index n) : F :=
  if i=(d,s) then 1 else 0
def column {n : Nat} (alpha : F) (d : Fin n) (s : Fin 4) (i : Index n) : F :=
  unit d s i-alpha^s.val*unit d 0 i
def localCoeff {n : Nat} (quarter alpha : F) (d : Fin n) (s : Fin 4)
    (w : Index n → F) (k : Nat) : F :=
  (∑ b : Fin 4, if s.val+(4-b.val)%4=k then quarter*w (d,b) else 0) -
    alpha^s.val*(∑ b : Fin 4, if (4-b.val)%4=k then quarter*w (d,b) else 0)

theorem unit_coefficient {n : Nat} (quarter : F) (d : Fin n) (s : Fin 4)
    (w : Index n → F) (k : Nat) :
    coefficient (sourceKernel n k quarter) (unit d s) w =
      ∑ b : Fin 4, if s.val+(4-b.val)%4=k then quarter*w (d,b) else 0 := by
  simp [coefficient, unit, mul_ite, Finset.sum_ite_irrel, Fintype.sum_prod_type,
    sourceKernel, ite_and]

theorem column_coefficient {n : Nat} (quarter alpha : F) (d : Fin n) (s : Fin 4)
    (w : Index n → F) (k : Nat) :
    coefficient (sourceKernel n k quarter) (column alpha d s) w =
      localCoeff quarter alpha d s w k := by
  have h := coefficient_left (sourceKernel n k quarter) (unit d s) (unit d 0) w
    (1:F) (-(alpha^s.val))
  change coefficient (sourceKernel n k quarter)
    (fun i => unit d s i-alpha^s.val*unit d 0 i) w = _
  simpa [localCoeff, unit_coefficient, sub_eq_add_neg] using h

theorem column_point {n : Nat} (alpha : F) (d : Fin n) (s : Fin 4)
    (w : Index n → F) :
    (∑ i, column alpha d s i*w i) = w (d,s)-alpha^s.val*w (d,0) := by
  simp [column, unit, sub_mul, mul_ite, Finset.sum_sub_distrib]

theorem point_high {n : Nat} (b : Nat) (q v w : Index n → F)
    (same : ∀ i, b ≤ i.1.val → q i=v i)
    (low : ∀ i, i.1.val<b → w i=0) :
    (∑ i, q i*w i) = ∑ i, v i*w i := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b ≤ i.1.val
  · rw [same i hi]
  · rw [low i (by omega)]; simp

theorem coefficient_high {n : Nat} (b k : Nat) (quarter : F) (q v w : Index n → F)
    (same : ∀ i, b ≤ i.1.val → q i=v i)
    (low : ∀ i, i.1.val<b → w i=0) :
    coefficient (sourceKernel n k quarter) q w =
      coefficient (sourceKernel n k quarter) v w := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : b ≤ i.1.val
  · rw [same i hi]
  · by_cases hij : i.1=j.1
    · rw [low j (by have := congrArg Fin.val hij; omega)]; simp
    · simp [sourceKernel,hij]

#print axioms unit_coefficient
#print axioms column_coefficient
#print axioms column_point
#print axioms point_high
#print axioms coefficient_high
end
end AspisR19.HighRepairInvariant
