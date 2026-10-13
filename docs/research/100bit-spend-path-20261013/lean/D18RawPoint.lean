import R1D18PointWeights
import R1RawFunctionalWeights

/-! D18 tensor rows induce the explicit Boolean row functional after transport.
This composes the checked D18 product with the R1 raw-row linear map. It does
not import the historical semantic opening object or identify Rust operations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.D18RawPoint
open scoped BigOperators
variable {K E : Type} [Field K] [Field E]

/-- Boolean row weight with points in the source's MSB-first order. -/
def booleanRow (p : Fin 10 → K) (r : Fin 1024) : K :=
  ∏ b : Fin 10, if r.val / 2 ^ b.val % 2 = 0 then
    1 - p ⟨9 - b.val, by have := b.isLt; omega⟩
    else p ⟨9 - b.val, by have := b.isLt; omega⟩

theorem tensorPoint_eq_booleanRow (p : Fin 10 → K) (j : Fin 1024) :
    tensorPoint p j = booleanRow p (row j) :=
  (rowPoint_eq_tensorPoint p j).symm

-- Definitional alignment of the 1024-coordinate finite-function linear map.
set_option maxRecDepth 4096 in
theorem pointRowMap_eq_row_sum (iota : K →+* E)
    (p : Fin 10 → K) (m : Fin 1024 → E) :
    AspisR1.RawFunctionalWeights.rowMap iota (tensorPoint p) m =
      ∑ r : Fin 1024, m (row r) * iota (booleanRow p r) := by
  change (∑ j : Fin 1024, m j * iota (tensorPoint p j)) = _
  simp_rw [tensorPoint_eq_booleanRow]
  have h : (∑ r : Fin 1024,
      m (row r) * iota (booleanRow p (row (row r)))) =
      ∑ j : Fin 1024, m j * iota (booleanRow p (row j)) :=
    Equiv.sum_comp rowEquiv (fun j => m j * iota (booleanRow p (row j)))
  simpa only [row_involutive] using h.symm

#print axioms tensorPoint_eq_booleanRow
#print axioms pointRowMap_eq_row_sum
end AspisR1.D18RawPoint
end
