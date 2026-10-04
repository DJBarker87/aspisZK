import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk03
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row140_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 140 ↔
      i.val ∈ ([11, 12, 13, 14] : List Nat) := by
  revert i
  decide

theorem row140_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([11, 12, 13, 14] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 140 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row140_support i).mp hs)

#print axioms row140_support
#print axioms row140_source_zero
theorem row142_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 142 ↔
      i.val ∈ ([13, 14] : List Nat) := by
  revert i
  decide

theorem row142_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([13, 14] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 142 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row142_support i).mp hs)

#print axioms row142_support
#print axioms row142_source_zero
theorem row144_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 144 ↔
      i.val ∈ ([13, 14, 15, 16, 17, 18, 21, 22] : List Nat) := by
  revert i
  decide

theorem row144_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([13, 14, 15, 16, 17, 18, 21, 22] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 144 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row144_support i).mp hs)

#print axioms row144_support
#print axioms row144_source_zero
theorem row146_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 146 ↔
      i.val ∈ ([15, 16] : List Nat) := by
  revert i
  decide

theorem row146_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([15, 16] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 146 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row146_support i).mp hs)

#print axioms row146_support
#print axioms row146_source_zero
end AspisV8R19.R800SelectedSupportChunk03
