import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk01
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row124_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 124 ↔
      i.val ∈ ([3, 4, 5, 6] : List Nat) := by
  revert i
  decide

theorem row124_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([3, 4, 5, 6] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 124 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row124_support i).mp hs)

#print axioms row124_support
#print axioms row124_source_zero
theorem row126_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 126 ↔
      i.val ∈ ([5, 6] : List Nat) := by
  revert i
  decide

theorem row126_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([5, 6] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 126 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row126_support i).mp hs)

#print axioms row126_support
#print axioms row126_source_zero
theorem row128_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 128 ↔
      i.val ∈ ([5, 6, 7, 8, 9, 10, 13, 14, 21, 22, 35, 65] : List Nat) := by
  revert i
  decide

theorem row128_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([5, 6, 7, 8, 9, 10, 13, 14, 21, 22, 35, 65] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 128 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row128_support i).mp hs)

#print axioms row128_support
#print axioms row128_source_zero
theorem row130_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 130 ↔
      i.val ∈ ([7, 8, 221] : List Nat) := by
  revert i
  decide

theorem row130_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([7, 8, 221] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 130 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row130_support i).mp hs)

#print axioms row130_support
#print axioms row130_source_zero
end AspisV8R19.R800SelectedSupportChunk01
