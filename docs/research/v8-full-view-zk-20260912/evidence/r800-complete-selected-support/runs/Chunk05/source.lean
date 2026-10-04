import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk05
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row156_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 156 ↔
      i.val ∈ ([19, 20, 21, 22] : List Nat) := by
  revert i
  decide

theorem row156_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([19, 20, 21, 22] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 156 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row156_support i).mp hs)

#print axioms row156_support
#print axioms row156_source_zero
theorem row158_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 158 ↔
      i.val ∈ ([21, 22] : List Nat) := by
  revert i
  decide

theorem row158_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([21, 22] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 158 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row158_support i).mp hs)

#print axioms row158_support
#print axioms row158_source_zero
theorem row160_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 160 ↔
      i.val ∈ ([21, 22, 23, 24, 25, 26, 29, 30, 35] : List Nat) := by
  revert i
  decide

theorem row160_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([21, 22, 23, 24, 25, 26, 29, 30, 35] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 160 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row160_support i).mp hs)

#print axioms row160_support
#print axioms row160_source_zero
theorem row162_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 162 ↔
      i.val ∈ ([23, 24, 221] : List Nat) := by
  revert i
  decide

theorem row162_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([23, 24, 221] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 162 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row162_support i).mp hs)

#print axioms row162_support
#print axioms row162_source_zero
end AspisV8R19.R800SelectedSupportChunk05
