import AspisV8R19.R738JointObservationModel
import AspisV8R17.SourceChordTranspose
import AspisV8R17.TransportedOpening

/-! Sparse point-row evaluation through the exact source transport and chord
transpose.  No rank, tail, native execution, or oracle premise is used. -/
set_option autoImplicit false
namespace AspisV8R19.R740SparsePointObservation
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R738JointObservationModel
open scoped BigOperators
noncomputable section
variable {F : Type*} [CommRing F]

def pointWeight (half a b c : F) (point : Fin 10 → F) : Nat → F :=
  sourceChordTranspose half
    (extendFin1024 (transportDual TwoSwapSourceTable.inactive 1023 TwoSwapSourceTable.order
      (fun i => sourcePointBasis point i.val))) a b c

theorem point_transport_pairing (half a b c : F) (point : Fin 10 → F)
    (q : Nat → F) :
    sourcePointFunctional point (inverseTransport TwoSwapSourceTable.inactive 1023
      TwoSwapSourceTable.order (fun j => sourceChord half q a b c j.val)) =
      rangeDot 1024 (pointWeight half a b c point) q := by
  unfold sourcePointFunctional pointWeight
  rw [inverseTransport_dot]
  rw [← rangeDot_extendFin1024]
  exact source_chord_transpose_pairing half q _ a b c

theorem rangeDot_unitVector (n k : Nat) (hk : k < n) (w : Nat → F) :
    rangeDot n w (unitVector k) = w k := by
  simp [rangeDot,unitVector,Finset.sum_ite_eq',hk]

theorem qPair_point_observation (half a b c alpha : F) (point : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) :
    sourcePointFunctional point (inverseTransport TwoSwapSourceTable.inactive 1023
      TwoSwapSourceTable.order (fun j => sourceChord half (qPair alpha d s) a b c j.val)) =
      pointWeight half a b c point (4*d.val+s.val+1)-
        alpha^(s.val+1)*pointWeight half a b c point (4*d.val) := by
  rw [point_transport_pairing]
  unfold qPair
  rw [rangeDot_sub_right,rangeDot_scale_right]
  rw [rangeDot_unitVector 1024 (4*d.val+s.val+1) (by omega),
    rangeDot_unitVector 1024 (4*d.val) (by omega)]

theorem direction_point_observation (half a b c alpha : F) (point : Fin 10 → F)
    (d : Fin 255) (s : Fin 3) :
    sourcePointFunctional point (inverseTransport TwoSwapSourceTable.inactive 1023
      TwoSwapSourceTable.order (fun j => sourceChord half (direction alpha d s) a b c j.val)) =
      (pointWeight half a b c point (4*d.val+s.val+1)-
        alpha^(s.val+1)*pointWeight half a b c point (4*d.val))-
      (pointWeight half a b c point (s.val+1)-
        alpha^(s.val+1)*pointWeight half a b c point 0) := by
  rw [point_transport_pairing]
  unfold direction qPair
  rw [rangeDot_sub_right]
  rw [rangeDot_sub_right,rangeDot_scale_right,
    rangeDot_sub_right,rangeDot_scale_right]
  norm_num only [Fin.val_zero,Nat.mul_zero,zero_add]
  rw [rangeDot_unitVector 1024 (4*d.val+s.val+1) (by omega),
    rangeDot_unitVector 1024 (4*d.val) (by omega),
    rangeDot_unitVector 1024 (s.val+1) (by omega),
    rangeDot_unitVector 1024 0 (by omega)]

#print axioms point_transport_pairing
#print axioms rangeDot_unitVector
#print axioms qPair_point_observation
#print axioms direction_point_observation
end
end AspisV8R19.R740SparsePointObservation
