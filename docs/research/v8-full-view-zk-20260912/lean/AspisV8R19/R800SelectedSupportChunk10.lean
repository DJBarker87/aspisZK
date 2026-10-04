import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk10
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row204_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 204 ↔
      i.val ∈ ([39, 40, 41, 42] : List Nat) := by
  revert i
  decide

theorem row204_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([39, 40, 41, 42] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 204 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row204_support i).mp hs)

#print axioms row204_support
#print axioms row204_source_zero
theorem row206_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 206 ↔
      i.val ∈ ([41, 42] : List Nat) := by
  revert i
  decide

theorem row206_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([41, 42] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 206 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row206_support i).mp hs)

#print axioms row206_support
#print axioms row206_source_zero
theorem row208_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 208 ↔
      i.val ∈ ([41, 42, 43, 44, 45, 46, 49, 50] : List Nat) := by
  revert i
  decide

theorem row208_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([41, 42, 43, 44, 45, 46, 49, 50] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 208 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row208_support i).mp hs)

#print axioms row208_support
#print axioms row208_source_zero
theorem row210_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 210 ↔
      i.val ∈ ([43, 44] : List Nat) := by
  revert i
  decide

theorem row210_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([43, 44] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 210 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row210_support i).mp hs)

#print axioms row210_support
#print axioms row210_source_zero
end AspisV8R19.R800SelectedSupportChunk10
