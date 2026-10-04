import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R743JointSparseEntryBinding
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748FiniteGatherSchedules
open AspisR19.SourceStatementPoints
noncomputable section
set_option maxRecDepth 4096
namespace AspisV8R19.R748LeafTest
abbrev M := ZMod 2147483647
def z : Fin 10 → M := ![1,1,2,3,4,2,2,3,0,2]
def point := SourceStatementPoints.points z 1
def w (i : Nat) : M := extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis point j.val)) i
lemma order190 : order (190 : Fin 1024) = (508 : Fin 1024) := by decide
lemma mem508 : (508 : Fin 1024) ∈ inactive.erase 1023 := by decide
lemma basis508 : sourcePointBasis point 508 = (576:M) := by
  norm_num [point, z, SourceStatementPoints.points, SourceStatementPoints.successor,
    SourceStatementPoints.reverseCoordinates, SourceStatementPoints.step,
    sourcePointBasis, sourceMultilinearFactors]
lemma basis1023 : sourcePointBasis point 1023 = (0:M) := by
  norm_num [point, z, SourceStatementPoints.points, SourceStatementPoints.successor,
    SourceStatementPoints.reverseCoordinates, SourceStatementPoints.step,
    sourcePointBasis, sourceMultilinearFactors]
lemma w190 : w 190 = 576 := by
  unfold w
  simp only [extendFin1024, Nat.reduceLT, ↓reduceIte]
  unfold transportDual
  rw [order190, if_pos mem508]
  norm_num [basis508, basis1023]
end AspisV8R19.R748LeafTest
