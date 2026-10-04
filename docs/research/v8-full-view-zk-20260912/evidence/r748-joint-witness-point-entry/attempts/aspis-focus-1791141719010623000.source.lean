import AspisV8R19.R748FiniteGatherSchedules
import AspisV8R19.R743JointSparseEntryBinding
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R748FiniteGatherSchedules
open AspisR19.SourceStatementPoints
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace AspisV8R19.R748JointWitnessPointEntry
abbrev M := ZMod 2147483647
def z : Fin 10 → M := ![1,1,2,3,4,2,2,3,0,2]
def point := SourceStatementPoints.points z 1
def p : Fin 10 → M := ![1,1,2,3,4,2,2,3,2,-1]
def w (i : Nat) : M := extendFin1024 (transportDual inactive 1023 order
    (fun j => sourcePointBasis point j.val)) i
lemma point_eq_p : point = p := by
  funext i
  unfold point
  rw [SourceStatementPoints.points_eq]
  fin_cases i <;> norm_num [ResidualModel.point, ResidualModel.carry, z,
    Fin.prod_univ_succ, p]
lemma order_0 : order (0 : Fin 1024) = (14 : Fin 1024) := by decide
lemma w_0 : w 0 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (0 : Fin 1024) = 576
  unfold transportDual
  rw [order_0, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_1 : order (1 : Fin 1024) = (15 : Fin 1024) := by decide
lemma w_1 : w 1 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (1 : Fin 1024) = 576
  unfold transportDual
  rw [order_1, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_2 : order (2 : Fin 1024) = (30 : Fin 1024) := by decide
lemma w_2 : w 2 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (2 : Fin 1024) = 576
  unfold transportDual
  rw [order_2, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_3 : order (3 : Fin 1024) = (31 : Fin 1024) := by decide
lemma w_3 : w 3 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (3 : Fin 1024) = 576
  unfold transportDual
  rw [order_3, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_5 : order (5 : Fin 1024) = (47 : Fin 1024) := by decide
lemma w_5 : w 5 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (5 : Fin 1024) = 576
  unfold transportDual
  rw [order_5, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_6 : order (6 : Fin 1024) = (62 : Fin 1024) := by decide
lemma w_6 : w 6 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (6 : Fin 1024) = 576
  unfold transportDual
  rw [order_6, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_129 : order (129 : Fin 1024) = (13 : Fin 1024) := by decide
lemma w_129 : w 129 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (129 : Fin 1024) = 576
  unfold transportDual
  rw [order_129, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_130 : order (130 : Fin 1024) = (28 : Fin 1024) := by decide
lemma w_130 : w 130 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (130 : Fin 1024) = 0
  unfold transportDual
  rw [order_130, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_161 : order (161 : Fin 1024) = (269 : Fin 1024) := by decide
lemma w_161 : w 161 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (161 : Fin 1024) = 576
  unfold transportDual
  rw [order_161, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_162 : order (162 : Fin 1024) = (284 : Fin 1024) := by decide
lemma w_162 : w 162 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (162 : Fin 1024) = 0
  unfold transportDual
  rw [order_162, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_177 : order (177 : Fin 1024) = (397 : Fin 1024) := by decide
lemma w_177 : w 177 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (177 : Fin 1024) = 576
  unfold transportDual
  rw [order_177, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_178 : order (178 : Fin 1024) = (412 : Fin 1024) := by decide
lemma w_178 : w 178 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (178 : Fin 1024) = 0
  unfold transportDual
  rw [order_178, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_185 : order (185 : Fin 1024) = (461 : Fin 1024) := by decide
lemma w_185 : w 185 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (185 : Fin 1024) = 576
  unfold transportDual
  rw [order_185, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_186 : order (186 : Fin 1024) = (476 : Fin 1024) := by decide
lemma w_186 : w 186 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (186 : Fin 1024) = 576
  unfold transportDual
  rw [order_186, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_188 : order (188 : Fin 1024) = (492 : Fin 1024) := by decide
lemma w_188 : w 188 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (188 : Fin 1024) = 576
  unfold transportDual
  rw [order_188, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_189 : order (189 : Fin 1024) = (493 : Fin 1024) := by decide
lemma w_189 : w 189 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (189 : Fin 1024) = 576
  unfold transportDual
  rw [order_189, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_190 : order (190 : Fin 1024) = (508 : Fin 1024) := by decide
lemma w_190 : w 190 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (190 : Fin 1024) = 0
  unfold transportDual
  rw [order_190, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_191 : order (191 : Fin 1024) = (509 : Fin 1024) := by decide
lemma w_191 : w 191 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (191 : Fin 1024) = 576
  unfold transportDual
  rw [order_191, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_193 : order (193 : Fin 1024) = (525 : Fin 1024) := by decide
lemma w_193 : w 193 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (193 : Fin 1024) = 576
  unfold transportDual
  rw [order_193, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_194 : order (194 : Fin 1024) = (540 : Fin 1024) := by decide
lemma w_194 : w 194 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (194 : Fin 1024) = 0
  unfold transportDual
  rw [order_194, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]

def pw : Nat → M := pointWeight (1073741824:M) 7 5 (-5) point
lemma pw191 : pw 191 = 7632 := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  rw [gatherGather95, gather95]
  change
    -(5 * (w 190 - ((1073741824:M)*w 190 + (1073741824:M)^2*w 186 +
      (1073741824:M)^3*w 178 + (1073741824:M)^4*w 162 +
      (1073741824:M)^5*w 130 + (1073741824:M)^5*w 194))) +
      7*w 191 + 5*((1073741824:M)*w 189 + (1073741824:M)^2*w 185 +
      (1073741824:M)^3*w 177 + (1073741824:M)^4*w 161 +
      (1073741824:M)^5*w 129 + (1073741824:M)^5*w 193) = 7632
  rw [w_190,w_186,w_178,w_162,w_130,w_194,w_191,w_189,w_185,w_177,w_161,w_129,w_193]
  norm_num

#print axioms pw191
end AspisV8R19.R748JointWitnessPointEntry
