import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk02
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row132_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 132 ↔
      i.val ∈ ([7, 8, 9, 10] : List Nat) := by
  revert i
  decide

theorem row132_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([7, 8, 9, 10] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 132 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row132_support i).mp hs)

#print axioms row132_support
#print axioms row132_source_zero
theorem row134_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 134 ↔
      i.val ∈ ([9, 10] : List Nat) := by
  revert i
  decide

theorem row134_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([9, 10] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 134 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row134_support i).mp hs)

#print axioms row134_support
#print axioms row134_source_zero
theorem row136_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 136 ↔
      i.val ∈ ([9, 10, 11, 12, 13, 14] : List Nat) := by
  revert i
  decide

theorem row136_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([9, 10, 11, 12, 13, 14] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 136 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row136_support i).mp hs)

#print axioms row136_support
#print axioms row136_source_zero
theorem row138_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 138 ↔
      i.val ∈ ([11, 12] : List Nat) := by
  revert i
  decide

theorem row138_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([11, 12] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 138 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row138_support i).mp hs)

#print axioms row138_support
#print axioms row138_source_zero
end AspisV8R19.R800SelectedSupportChunk02
