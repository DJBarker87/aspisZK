import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk34
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row632_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 632 ↔
      i.val ∈ ([135, 136, 137, 138, 139, 140] : List Nat) := by
  revert i
  decide

theorem row632_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([135, 136, 137, 138, 139, 140] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 632 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row632_support i).mp hs)

#print axioms row632_support
#print axioms row632_source_zero
theorem row634_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 634 ↔
      i.val ∈ ([137, 138, 141] : List Nat) := by
  revert i
  decide

theorem row634_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([137, 138, 141] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 634 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row634_support i).mp hs)

#print axioms row634_support
#print axioms row634_source_zero
theorem row636_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 636 ↔
      i.val ∈ ([137, 138, 139, 140, 141] : List Nat) := by
  revert i
  decide

theorem row636_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([137, 138, 139, 140, 141] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 636 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row636_support i).mp hs)

#print axioms row636_support
#print axioms row636_source_zero
theorem row638_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 638 ↔
      i.val ∈ ([139, 140, 141] : List Nat) := by
  revert i
  decide

theorem row638_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([139, 140, 141] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 638 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row638_support i).mp hs)

#print axioms row638_support
#print axioms row638_source_zero
end AspisV8R19.R800SelectedSupportChunk34
