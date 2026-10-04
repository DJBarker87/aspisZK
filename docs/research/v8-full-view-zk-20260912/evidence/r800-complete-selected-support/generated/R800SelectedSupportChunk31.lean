import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk31
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row380_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 380 ↔
      i.val ∈ ([123, 124, 125, 126] : List Nat) := by
  revert i
  decide

theorem row380_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([123, 124, 125, 126] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 380 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row380_support i).mp hs)

#print axioms row380_support
#print axioms row380_source_zero
theorem row382_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 382 ↔
      i.val ∈ ([125, 126] : List Nat) := by
  revert i
  decide

theorem row382_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([125, 126] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 382 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row382_support i).mp hs)

#print axioms row382_support
#print axioms row382_source_zero
theorem row499_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 499 ↔
      i.val ∈ ([127] : List Nat) := by
  revert i
  decide

theorem row499_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([127] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 499 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row499_support i).mp hs)

#print axioms row499_support
#print axioms row499_source_zero
theorem row501_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 501 ↔
      i.val ∈ ([127, 128, 129] : List Nat) := by
  revert i
  decide

theorem row501_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([127, 128, 129] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 501 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row501_support i).mp hs)

#print axioms row501_support
#print axioms row501_source_zero
end AspisV8R19.R800SelectedSupportChunk31
