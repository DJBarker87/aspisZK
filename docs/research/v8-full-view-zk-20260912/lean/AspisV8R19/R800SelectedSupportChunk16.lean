import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk16
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row253_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 253 ↔
      i.val ∈ ([64, 65] : List Nat) := by
  revert i
  decide

theorem row253_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([64, 65] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 253 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row253_support i).mp hs)

#print axioms row253_support
#print axioms row253_source_zero
theorem row257_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 257 ↔
      i.val ∈ ([66, 67, 69, 73, 81, 96, 133] : List Nat) := by
  revert i
  decide

theorem row257_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([66, 67, 69, 73, 81, 96, 133] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 257 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row257_support i).mp hs)

#print axioms row257_support
#print axioms row257_source_zero
theorem row259_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 259 ↔
      i.val ∈ ([66, 67] : List Nat) := by
  revert i
  decide

theorem row259_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([66, 67] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 259 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row259_support i).mp hs)

#print axioms row259_support
#print axioms row259_source_zero
theorem row261_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 261 ↔
      i.val ∈ ([67, 68, 69] : List Nat) := by
  revert i
  decide

theorem row261_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([67, 68, 69] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 261 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row261_support i).mp hs)

#print axioms row261_support
#print axioms row261_source_zero
end AspisV8R19.R800SelectedSupportChunk16
