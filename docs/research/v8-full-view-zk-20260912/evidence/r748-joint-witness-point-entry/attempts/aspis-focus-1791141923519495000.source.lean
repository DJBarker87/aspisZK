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
lemma inactive_0 : isInactive (14 : Fin 1024) = true := by decide
lemma mem_0 : (14 : Fin 1024) ∈ inactive.erase 1023 := by
  change (14 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_0⟩
lemma w_0 : w 0 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (0 : Fin 1024) = 576
  unfold transportDual
  rw [order_0, if_pos mem_0, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_1 : order (1 : Fin 1024) = (15 : Fin 1024) := by decide
lemma inactive_1 : isInactive (15 : Fin 1024) = true := by decide
lemma mem_1 : (15 : Fin 1024) ∈ inactive.erase 1023 := by
  change (15 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_1⟩
lemma w_1 : w 1 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (1 : Fin 1024) = 576
  unfold transportDual
  rw [order_1, if_pos mem_1, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_2 : order (2 : Fin 1024) = (30 : Fin 1024) := by decide
lemma inactive_2 : isInactive (30 : Fin 1024) = true := by decide
lemma mem_2 : (30 : Fin 1024) ∈ inactive.erase 1023 := by
  change (30 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_2⟩
lemma w_2 : w 2 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (2 : Fin 1024) = 576
  unfold transportDual
  rw [order_2, if_pos mem_2, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_3 : order (3 : Fin 1024) = (31 : Fin 1024) := by decide
lemma inactive_3 : isInactive (31 : Fin 1024) = true := by decide
lemma mem_3 : (31 : Fin 1024) ∈ inactive.erase 1023 := by
  change (31 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_3⟩
lemma w_3 : w 3 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (3 : Fin 1024) = 576
  unfold transportDual
  rw [order_3, if_pos mem_3, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_5 : order (5 : Fin 1024) = (47 : Fin 1024) := by decide
lemma inactive_5 : isInactive (47 : Fin 1024) = true := by decide
lemma mem_5 : (47 : Fin 1024) ∈ inactive.erase 1023 := by
  change (47 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_5⟩
lemma w_5 : w 5 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (5 : Fin 1024) = 576
  unfold transportDual
  rw [order_5, if_pos mem_5, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_6 : order (6 : Fin 1024) = (62 : Fin 1024) := by decide
lemma inactive_6 : isInactive (62 : Fin 1024) = true := by decide
lemma mem_6 : (62 : Fin 1024) ∈ inactive.erase 1023 := by
  change (62 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_6⟩
lemma w_6 : w 6 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (6 : Fin 1024) = 576
  unfold transportDual
  rw [order_6, if_pos mem_6, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_129 : order (129 : Fin 1024) = (13 : Fin 1024) := by decide
lemma inactive_129 : isInactive (13 : Fin 1024) = true := by decide
lemma mem_129 : (13 : Fin 1024) ∈ inactive.erase 1023 := by
  change (13 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_129⟩
lemma w_129 : w 129 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (129 : Fin 1024) = 576
  unfold transportDual
  rw [order_129, if_pos mem_129, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_130 : order (130 : Fin 1024) = (28 : Fin 1024) := by decide
lemma inactive_130 : isInactive (28 : Fin 1024) = false := by decide
lemma notmem_130 : (28 : Fin 1024) ∉ inactive.erase 1023 := by
  intro h
  change (28 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
  have hi := (Finset.mem_erase.mp h).2
  rw [T163SourceTable.inactive, Finset.mem_filter] at hi
  have hb := hi.2
  have hfalse : T163SourceTable.isInactive (28 : Fin 1024) = false := by exact inactive_130
  rw [hfalse] at hb
  decide
lemma w_130 : w 130 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (130 : Fin 1024) = 0
  unfold transportDual
  rw [order_130, if_neg notmem_130, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_161 : order (161 : Fin 1024) = (269 : Fin 1024) := by decide
lemma inactive_161 : isInactive (269 : Fin 1024) = true := by decide
lemma mem_161 : (269 : Fin 1024) ∈ inactive.erase 1023 := by
  change (269 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_161⟩
lemma w_161 : w 161 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (161 : Fin 1024) = 576
  unfold transportDual
  rw [order_161, if_pos mem_161, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_162 : order (162 : Fin 1024) = (284 : Fin 1024) := by decide
lemma inactive_162 : isInactive (284 : Fin 1024) = false := by decide
lemma notmem_162 : (284 : Fin 1024) ∉ inactive.erase 1023 := by
  intro h
  change (284 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
  have hi := (Finset.mem_erase.mp h).2
  rw [T163SourceTable.inactive, Finset.mem_filter] at hi
  have hb := hi.2
  have hfalse : T163SourceTable.isInactive (284 : Fin 1024) = false := by exact inactive_162
  rw [hfalse] at hb
  decide
lemma w_162 : w 162 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (162 : Fin 1024) = 0
  unfold transportDual
  rw [order_162, if_neg notmem_162, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_177 : order (177 : Fin 1024) = (397 : Fin 1024) := by decide
lemma inactive_177 : isInactive (397 : Fin 1024) = true := by decide
lemma mem_177 : (397 : Fin 1024) ∈ inactive.erase 1023 := by
  change (397 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_177⟩
lemma w_177 : w 177 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (177 : Fin 1024) = 576
  unfold transportDual
  rw [order_177, if_pos mem_177, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_178 : order (178 : Fin 1024) = (412 : Fin 1024) := by decide
lemma inactive_178 : isInactive (412 : Fin 1024) = false := by decide
lemma notmem_178 : (412 : Fin 1024) ∉ inactive.erase 1023 := by
  intro h
  change (412 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
  have hi := (Finset.mem_erase.mp h).2
  rw [T163SourceTable.inactive, Finset.mem_filter] at hi
  have hb := hi.2
  have hfalse : T163SourceTable.isInactive (412 : Fin 1024) = false := by exact inactive_178
  rw [hfalse] at hb
  decide
lemma w_178 : w 178 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (178 : Fin 1024) = 0
  unfold transportDual
  rw [order_178, if_neg notmem_178, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_185 : order (185 : Fin 1024) = (461 : Fin 1024) := by decide
lemma inactive_185 : isInactive (461 : Fin 1024) = true := by decide
lemma mem_185 : (461 : Fin 1024) ∈ inactive.erase 1023 := by
  change (461 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_185⟩
lemma w_185 : w 185 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (185 : Fin 1024) = 576
  unfold transportDual
  rw [order_185, if_pos mem_185, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_186 : order (186 : Fin 1024) = (476 : Fin 1024) := by decide
lemma inactive_186 : isInactive (476 : Fin 1024) = true := by decide
lemma mem_186 : (476 : Fin 1024) ∈ inactive.erase 1023 := by
  change (476 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_186⟩
lemma w_186 : w 186 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (186 : Fin 1024) = 576
  unfold transportDual
  rw [order_186, if_pos mem_186, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_188 : order (188 : Fin 1024) = (492 : Fin 1024) := by decide
lemma inactive_188 : isInactive (492 : Fin 1024) = true := by decide
lemma mem_188 : (492 : Fin 1024) ∈ inactive.erase 1023 := by
  change (492 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_188⟩
lemma w_188 : w 188 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (188 : Fin 1024) = 576
  unfold transportDual
  rw [order_188, if_pos mem_188, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_189 : order (189 : Fin 1024) = (493 : Fin 1024) := by decide
lemma inactive_189 : isInactive (493 : Fin 1024) = true := by decide
lemma mem_189 : (493 : Fin 1024) ∈ inactive.erase 1023 := by
  change (493 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_189⟩
lemma w_189 : w 189 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (189 : Fin 1024) = 576
  unfold transportDual
  rw [order_189, if_pos mem_189, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_190 : order (190 : Fin 1024) = (508 : Fin 1024) := by decide
lemma inactive_190 : isInactive (508 : Fin 1024) = false := by decide
lemma notmem_190 : (508 : Fin 1024) ∉ inactive.erase 1023 := by
  intro h
  change (508 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
  have hi := (Finset.mem_erase.mp h).2
  rw [T163SourceTable.inactive, Finset.mem_filter] at hi
  have hb := hi.2
  have hfalse : T163SourceTable.isInactive (508 : Fin 1024) = false := by exact inactive_190
  rw [hfalse] at hb
  decide
lemma w_190 : w 190 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (190 : Fin 1024) = 0
  unfold transportDual
  rw [order_190, if_neg notmem_190, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_191 : order (191 : Fin 1024) = (509 : Fin 1024) := by decide
lemma inactive_191 : isInactive (509 : Fin 1024) = true := by decide
lemma mem_191 : (509 : Fin 1024) ∈ inactive.erase 1023 := by
  change (509 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_191⟩
lemma w_191 : w 191 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (191 : Fin 1024) = 576
  unfold transportDual
  rw [order_191, if_pos mem_191, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_193 : order (193 : Fin 1024) = (525 : Fin 1024) := by decide
lemma inactive_193 : isInactive (525 : Fin 1024) = true := by decide
lemma mem_193 : (525 : Fin 1024) ∈ inactive.erase 1023 := by
  change (525 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023
  rw [Finset.mem_erase]
  constructor
  · decide
  · rw [T163SourceTable.inactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by exact inactive_193⟩
lemma w_193 : w 193 = (576:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (193 : Fin 1024) = 576
  unfold transportDual
  rw [order_193, if_pos mem_193, point_eq_p]
  simp +decide [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p]
lemma order_194 : order (194 : Fin 1024) = (540 : Fin 1024) := by decide
lemma inactive_194 : isInactive (540 : Fin 1024) = false := by decide
lemma notmem_194 : (540 : Fin 1024) ∉ inactive.erase 1023 := by
  intro h
  change (540 : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h
  have hi := (Finset.mem_erase.mp h).2
  rw [T163SourceTable.inactive, Finset.mem_filter] at hi
  have hb := hi.2
  have hfalse : T163SourceTable.isInactive (540 : Fin 1024) = false := by exact inactive_194
  rw [hfalse] at hb
  decide
lemma w_194 : w 194 = (0:M) := by
  unfold w extendFin1024
  rw [dif_pos (by omega)]
  change transportDual inactive 1023 order (fun j => sourcePointBasis point j.val)
      (194 : Fin 1024) = 0
  unfold transportDual
  rw [order_194, if_neg notmem_194, point_eq_p]
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
  decide

lemma pw188 : pw 188 = 1152 := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  rw [gather94]
  change 7*w 188 + 5*w 190 - 5*w 189 = 1152
  rw [w_188,w_190,w_189]
  decide

lemma pw3 : pw 3 = 6912 := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualOdd
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  rw [gatherGather1, gather1]
  change -(5 * (w 2 - ((1073741824:M)*w 2 + (1073741824:M)*w 6))) +
      7*w 3 + 5*((1073741824:M)*w 1 + (1073741824:M)*w 5) = 6912
  rw [w_2,w_6,w_3,w_1,w_5]
  decide

lemma pw0 : pw 0 = 4032 := by
  unfold pw pointWeight sourceChordTranspose
  unfold interleave chordDualEven
  simp only [Nat.reduceMod, Nat.reduceDiv, ↓reduceIte]
  rw [gather0]
  change 7*w 0 + 5*w 2 - 5*w 1 = 4032
  rw [w_0,w_2,w_1]
  decide

lemma fixed_point_entry :
    sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 2
      (.inr (.inl 1)) = 988560 := by
  unfold sparseObservation
  change (pw 191 - 7^(2+1)*pw 188) - (pw 3 - 7^(2+1)*pw 0) = 988560
  rw [pw191,pw188,pw3,pw0]
  decide

#print axioms gather95
#print axioms pw191
#print axioms pw188
#print axioms pw3
#print axioms pw0
#print axioms fixed_point_entry
end AspisV8R19.R748JointWitnessPointEntry
