import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk09
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row196_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 196 ↔
      i.val ∈ ([36, 37, 38] : List Nat) := by
  revert i
  decide

theorem row196_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([36, 37, 38] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 196 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row196_support i).mp hs)

#print axioms row196_support
#print axioms row196_source_zero
theorem row198_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 198 ↔
      i.val ∈ ([37, 38] : List Nat) := by
  revert i
  decide

theorem row198_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([37, 38] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 198 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row198_support i).mp hs)

#print axioms row198_support
#print axioms row198_source_zero
theorem row200_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 200 ↔
      i.val ∈ ([37, 38, 39, 40, 41, 42] : List Nat) := by
  revert i
  decide

theorem row200_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([37, 38, 39, 40, 41, 42] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 200 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row200_support i).mp hs)

#print axioms row200_support
#print axioms row200_source_zero
theorem row202_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 202 ↔
      i.val ∈ ([39, 40] : List Nat) := by
  revert i
  decide

theorem row202_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([39, 40] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 202 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row202_support i).mp hs)

#print axioms row202_support
#print axioms row202_source_zero
end AspisV8R19.R800SelectedSupportChunk09
