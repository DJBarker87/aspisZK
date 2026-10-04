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
def p : Fin 10 → M := ![1,1,2,3,4,2,2,3,2,-1]
lemma point_eq_p : point = p := by
  funext i
  unfold point
  rw [SourceStatementPoints.points_eq]
  fin_cases i <;> norm_num [ResidualModel.point, ResidualModel.carry, z,
    Fin.prod_univ_succ, p]
lemma order190 : order (190 : Fin 1024) = (508 : Fin 1024) := by decide
lemma notmem508 : (508 : Fin 1024) ∉ inactive.erase 1023 := by decide
lemma basis508 : sourcePointBasis point 508 = (0:M) := by
  rw [point_eq_p]
  simp +decide [p, sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ]
lemma w190 : w 190 = 0 := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (190 : Fin 1024) = 0
  unfold transportDual
  rw [order190, if_neg notmem508]
  simpa using basis508
end AspisV8R19.R748LeafTest
