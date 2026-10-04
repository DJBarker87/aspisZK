import AspisV8R19.R748JointWitnessPointEntry
import AspisV8R19.R750WitnessPointSupport

namespace AspisR19.R752SharedWitnessPointSupport
open AspisV8R17
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

private def c0 : Fin 10 := ⟨0, by omega⟩
private def c1 : Fin 10 := ⟨1, by omega⟩
private def c8 : Fin 10 := ⟨8, by omega⟩

/-- A source-selected zero bit at one coordinate where the point value is one
zeros that exact multilinear factor. -/
theorem source_basis_zero_at_one (point : Fin 10 → F) (i : Nat)
    (coordinate : Fin 10) (hpoint : point coordinate = 1)
    (hbit : ((i >>> (9-coordinate.val)) &&& 1) = 0) :
    sourcePointBasis point i = 0 := by
  have hfactor :
      (if ((i >>> (9-coordinate.val)) &&& 1) = 0
       then 1-point coordinate else point coordinate) = 0 := by
    simp [hbit, hpoint]
  simp only [sourcePointBasis, sourceMultilinearFactors, List.prod_ofFn]
  exact Finset.prod_eq_zero (Finset.mem_univ coordinate) hfactor

/-- Coordinates 0 and 1 of this source point are both one. -/
theorem source_basis_zero_of_first_two_one (point : Fin 10 → F) (i : Nat)
    (h0 : point c0 = 1) (h1 : point c1 = 1)
    (hbits : (((i >>> 9) &&& 1) = 0) ∨ (((i >>> 8) &&& 1) = 0)) :
    sourcePointBasis point i = 0 := by
  rcases hbits with h9 | h8
  · exact source_basis_zero_at_one point i c0 h0 (by simpa [c0] using h9)
  · exact source_basis_zero_at_one point i c1 h1 (by simpa [c1] using h8)

/-- Coordinate 8 is zero, so choosing its source bit to be one zeros the basis. -/
theorem source_basis_zero_of_coord8_zero (point : Fin 10 → F) (i : Nat)
    (h8 : point c8 = 0) (hbit : ((i >>> 1) &&& 1) = 1) :
    sourcePointBasis point i = 0 := by
  have hfactor :
      (if ((i >>> (9-c8.val)) &&& 1) = 0
       then 1-point c8 else point c8) = 0 := by
    have hnot : ((i >>> (9-c8.val)) &&& 1) ≠ 0 := by
      change ((i >>> 1) &&& 1) ≠ 0
      rw [hbit]
      decide
    simp [hnot, h8]
  simp only [sourcePointBasis, sourceMultilinearFactors, List.prod_ofFn]
  exact Finset.prod_eq_zero (Finset.mem_univ c8) hfactor

/-- For the exact two-swap selected point 1, the first two source-bit cases
force a zero basis factor. -/
theorem point1_source_basis_zero (i : Nat)
    (hbits : (((i >>> 9) &&& 1) = 0) ∨ (((i >>> 8) &&& 1) = 0)) :
    sourcePointBasis AspisV8R19.R748JointWitnessPointEntry.point i = 0 := by
  have h0 : AspisV8R19.R748JointWitnessPointEntry.point c0 = 1 := by
    rw [AspisV8R19.R748JointWitnessPointEntry.point_eq_p]
    simp [c0, AspisV8R19.R748JointWitnessPointEntry.p]
  have h1 : AspisV8R19.R748JointWitnessPointEntry.point c1 = 1 := by
    rw [AspisV8R19.R748JointWitnessPointEntry.point_eq_p]
    simp [c1, AspisV8R19.R748JointWitnessPointEntry.p]
  exact source_basis_zero_of_first_two_one
    AspisV8R19.R748JointWitnessPointEntry.point i h0 h1 hbits

/-- The exact R750 point 2 has all three source-bit zero-factor cases. -/
theorem point2_source_basis_zero (i : Nat)
    (hbits : (((i >>> 9) &&& 1) = 0) ∨
      (((i >>> 8) &&& 1) = 0) ∨ (((i >>> 1) &&& 1) = 1)) :
    sourcePointBasis (AspisR19.SourceStatementPoints.points
      (AspisR19.R750WitnessPointSupport.zFin10 (F:=F)) 2) i = 0 := by
  have h0 : (AspisR19.SourceStatementPoints.points
      (AspisR19.R750WitnessPointSupport.zFin10 (F:=F)) 2) c0 = 1 := by
    rw [AspisR19.R750WitnessPointSupport.points2_exact]
    simp [c0]
  have h1 : (AspisR19.SourceStatementPoints.points
      (AspisR19.R750WitnessPointSupport.zFin10 (F:=F)) 2) c1 = 1 := by
    rw [AspisR19.R750WitnessPointSupport.points2_exact]
    simp [c1]
  have h8 : (AspisR19.SourceStatementPoints.points
      (AspisR19.R750WitnessPointSupport.zFin10 (F:=F)) 2) c8 = 0 := by
    rw [AspisR19.R750WitnessPointSupport.points2_exact]
    simp [c8]
  rcases hbits with h9 | h8bit | h1bit
  · exact source_basis_zero_at_one _ i c0 h0 (by simpa [c0] using h9)
  · exact source_basis_zero_at_one _ i c1 h1 (by simpa [c1] using h8bit)
  · exact source_basis_zero_of_coord8_zero _ i h8 (by simpa [c8] using h1bit)

#print axioms source_basis_zero_at_one
#print axioms source_basis_zero_of_first_two_one
#print axioms source_basis_zero_of_coord8_zero
#print axioms point1_source_basis_zero
#print axioms point2_source_basis_zero
end
end AspisR19.R752SharedWitnessPointSupport
