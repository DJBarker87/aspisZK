import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk06
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row164_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 164 ↔
      i.val ∈ ([23, 24, 25, 26] : List Nat) := by
  revert i
  decide

theorem row164_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([23, 24, 25, 26] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 164 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row164_support i).mp hs)

#print axioms row164_support
#print axioms row164_source_zero
theorem row166_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 166 ↔
      i.val ∈ ([25, 26] : List Nat) := by
  revert i
  decide

theorem row166_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([25, 26] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 166 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row166_support i).mp hs)

#print axioms row166_support
#print axioms row166_source_zero
theorem row168_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 168 ↔
      i.val ∈ ([25, 26, 27, 28, 29, 30] : List Nat) := by
  revert i
  decide

theorem row168_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([25, 26, 27, 28, 29, 30] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 168 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row168_support i).mp hs)

#print axioms row168_support
#print axioms row168_source_zero
theorem row170_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 170 ↔
      i.val ∈ ([27, 28] : List Nat) := by
  revert i
  decide

theorem row170_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([27, 28] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 170 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row170_support i).mp hs)

#print axioms row170_support
#print axioms row170_source_zero
end AspisV8R19.R800SelectedSupportChunk06
