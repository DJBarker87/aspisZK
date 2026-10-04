import AspisV8R19.R775GatherUnitChordBridge
import AspisV8R19.R746SelectedJointMinor
namespace AspisV8R19.R792JointSourceMatrixHom
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R744JointEntryHom
open AspisV8R19.R775GatherUnitChordBridge
open AspisV8R19.R746SelectedJointMinor
noncomputable section
set_option autoImplicit false
variable {F K : Type*} [CommRing F] [CommRing K]

lemma map_unit (f : F →+* K) (n r : Nat) :
    f (unitVector n r) = unitVector n r := by
  unfold unitVector
  split <;> simp

lemma map_chord_unit (f : F →+* K) (half a b c : F) (n r : Nat) (hn : n < 1024) :
    f (sourceChord half (unitVector n) a b c r) =
      sourceChord (f half) (unitVector n) (f a) (f b) (f c) r := by
  have hu (j : Nat) : (fun q => f (unitVector j q)) = unitVector j := by
    funext q; exact map_unit f j q
  by_cases he : n % 2 = 0
  · have hn' : n = 2*(n/2) := by omega
    rw [hn', sourceChord_unit_even_sourceGather half (n/2) r (by omega) a b c,
      sourceChord_unit_even_sourceGather (f half) (n/2) r (by omega) (f a) (f b) (f c)]
    split <;> simp only [map_add,map_mul,map_unit,map_sourceGather,hu]
  · have hn' : n = 2*(n/2)+1 := by omega
    rw [hn', sourceChord_unit_odd_sourceGather half (n/2) r (by omega) a b c,
      sourceChord_unit_odd_sourceGather (f half) (n/2) r (by omega) (f a) (f b) (f c)]
    split <;> simp only [map_add,map_sub,map_mul,map_unit,map_sourceGather,hu]

lemma map_chord_pair (f : F →+* K) (half a b c alpha : F)
    (d : Fin 255) (s : Fin 3) (r : Nat) :
    f (sourceChord half (qPair alpha d s) a b c r) =
      sourceChord (f half) (qPair (f alpha) d s) (f a) (f b) (f c) r := by
  unfold qPair
  rw [sourceChord_difference, sourceChord_difference]
  rw [map_sub,map_mul,map_pow,
    map_chord_unit f half a b c (4*d.val+s.val+1) r (by omega),
    map_chord_unit f half a b c (4*d.val) r (by omega)]

lemma map_chord_direction (f : F →+* K) (half a b c alpha : F)
    (d : Fin 255) (s : Fin 3) (r : Nat) :
    f (sourceChord half (direction alpha d s) a b c r) =
      sourceChord (f half) (direction (f alpha) d s) (f a) (f b) (f c) r := by
  have hdir (u v : Nat → F) : (fun i => u i-v i) = (fun i => u i-(1:F)*v i) := by
    funext i; simp
  have hdirK (u v : Nat → K) : (fun i => u i-v i) = (fun i => u i-(1:K)*v i) := by
    funext i; simp
  unfold direction
  rw [hdir,hdirK,sourceChord_difference,sourceChord_difference]
  simp only [one_mul,map_sub,map_chord_pair]

 theorem map_sparse_row (f : F →+* K) (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (d : Fin 255) (s : Fin 3)
    (row : R738JointObservationModel.ObservationRow) :
    f (sparseObservation half quarter a b c kappa tau alpha z d s row) =
      sparseObservation (f half) (f quarter) (f a) (f b) (f c) (f kappa) (f tau)
        (f alpha) (fun i => f (z i)) d s row := by
  rcases row with j | ⟨p | k⟩
  · exact map_chord_direction f half a b c alpha d s _
  · exact map_sparse_point_row f half quarter a b c kappa tau alpha z d s p
  · exact map_sparse_coefficient_row f half quarter a b c kappa tau alpha z d s k

 theorem map_chosen_matrix [Nontrivial F] [Nontrivial K] (f : F →+* K)
    (half quarter alpha u v kappa tau : F) (z : Fin 10 → F) :
    f.mapMatrix (chosenSourceMatrix half quarter alpha u v kappa tau z) =
      chosenSourceMatrix (f half) (f quarter) (f alpha) (f u) (f v) (f kappa) (f tau)
        (fun i => f (z i)) := by
  ext row col
  change f (chosenSourceMatrix half quarter alpha u v kappa tau z row col) =
    chosenSourceMatrix (f half) (f quarter) (f alpha) (f u) (f v) (f kappa) (f tau)
      (fun i => f (z i)) row col
  simp only [chosenSourceMatrix,
    rawObservation_indexedDirection,map_sparse_row,map_add,map_mul,map_sub,map_neg,map_one]

#print axioms map_chord_unit
#print axioms map_chord_pair
#print axioms map_chord_direction
#print axioms map_sparse_row
#print axioms map_chosen_matrix
end
end AspisV8R19.R792JointSourceMatrixHom
