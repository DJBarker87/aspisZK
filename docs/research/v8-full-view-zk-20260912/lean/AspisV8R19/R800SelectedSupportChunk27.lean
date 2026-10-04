import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk27
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row345_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 345 ↔
      i.val ∈ ([108, 109, 110, 112] : List Nat) := by
  revert i
  decide

theorem row345_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([108, 109, 110, 112] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 345 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row345_support i).mp hs)

#print axioms row345_support
#print axioms row345_source_zero
theorem row347_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 347 ↔
      i.val ∈ ([109, 110] : List Nat) := by
  revert i
  decide

theorem row347_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([109, 110] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 347 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row347_support i).mp hs)

#print axioms row347_support
#print axioms row347_source_zero
theorem row349_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 349 ↔
      i.val ∈ ([110, 111, 112] : List Nat) := by
  revert i
  decide

theorem row349_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([110, 111, 112] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 349 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row349_support i).mp hs)

#print axioms row349_support
#print axioms row349_source_zero
theorem row351_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 351 ↔
      i.val ∈ ([111, 112] : List Nat) := by
  revert i
  decide

theorem row351_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([111, 112] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 351 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row351_support i).mp hs)

#print axioms row351_support
#print axioms row351_source_zero
end AspisV8R19.R800SelectedSupportChunk27
