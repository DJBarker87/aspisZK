import AspisV8R19.SourceStatementPoints
import AspisV8R19.FullPointFunctional

namespace AspisR19.R750WitnessPointSupport
open AspisV8R17
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

def zFin10 (i : Fin 10) : F :=
  ([1,1,2,3,4,2,2,3,0,2] : List F).getD i.val 0

theorem points0_exact :
    AspisR19.SourceStatementPoints.points (zFin10 (F:=F)) 0 = zFin10 (F:=F) := by
  funext i
  rw [AspisR19.SourceStatementPoints.points_eq]
  fin_cases i <;> simp [zFin10, AspisR19.ResidualModel.point] <;> ring

theorem points2_exact :
    AspisR19.SourceStatementPoints.points (zFin10 (F:=F)) 2 =
      (fun i : Fin 10 => ([1,1,2,3,4,2,-1,-2,0,2] : List F).getD i.val 0) := by
  funext i
  rw [AspisR19.SourceStatementPoints.points_eq]
  fin_cases i <;> simp [zFin10, AspisR19.ResidualModel.point] <;> ring

/-- A zero factor at any of the three source coordinates makes the exact
source-shaped multilinear basis vanish; the index remains symbolic. -/
theorem source_basis_zero_of_bits (i : Nat)
    (hbits : (((i >>> 9) &&& 1) = 0) ∨
      (((i >>> 8) &&& 1) = 0) ∨ (((i >>> 1) &&& 1) = 1)) :
    sourcePointBasis (AspisR19.SourceStatementPoints.points (zFin10 (F:=F)) 0) i = 0 := by
  rw [points0_exact]
  rcases hbits with h9 | h8 | h1
  · have hz : (if (i >>> (9-(⟨0, by omega⟩ : Fin 10)).val) &&& 1 = 0
        then 1-zFin10 (F:=F) (⟨0, by omega⟩ : Fin 10)
        else zFin10 (F:=F) (⟨0, by omega⟩ : Fin 10)) = 0 := by
      simp [zFin10, h9]
    simp only [sourcePointBasis, sourceMultilinearFactors, List.prod_ofFn]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin 10)) hz
  · have hz : (if (i >>> (9-(⟨1, by omega⟩ : Fin 10)).val) &&& 1 = 0
        then 1-zFin10 (F:=F) (⟨1, by omega⟩ : Fin 10)
        else zFin10 (F:=F) (⟨1, by omega⟩ : Fin 10)) = 0 := by
      simp [zFin10, h8]
    simp only [sourcePointBasis, sourceMultilinearFactors, List.prod_ofFn]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨1, by omega⟩ : Fin 10)) hz
  · have hz : (if (i >>> (9-(⟨8, by omega⟩ : Fin 10)).val) &&& 1 = 0
        then 1-zFin10 (F:=F) (⟨8, by omega⟩ : Fin 10)
        else zFin10 (F:=F) (⟨8, by omega⟩ : Fin 10)) = 0 := by
      simp [zFin10, h1]
    simp only [sourcePointBasis, sourceMultilinearFactors, List.prod_ofFn]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨8, by omega⟩ : Fin 10)) hz

#print axioms points0_exact
#print axioms points2_exact
#print axioms source_basis_zero_of_bits
end
end AspisR19.R750WitnessPointSupport
