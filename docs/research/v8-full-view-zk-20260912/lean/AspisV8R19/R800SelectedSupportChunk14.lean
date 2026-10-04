import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk14
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row236_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 236 ↔
      i.val ∈ ([55, 56, 57, 58] : List Nat) := by
  revert i
  decide

theorem row236_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([55, 56, 57, 58] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 236 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row236_support i).mp hs)

#print axioms row236_support
#print axioms row236_source_zero
theorem row238_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 238 ↔
      i.val ∈ ([57, 58] : List Nat) := by
  revert i
  decide

theorem row238_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([57, 58] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 238 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row238_support i).mp hs)

#print axioms row238_support
#print axioms row238_source_zero
theorem row240_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 240 ↔
      i.val ∈ ([57, 58, 59, 60, 61, 65] : List Nat) := by
  revert i
  decide

theorem row240_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([57, 58, 59, 60, 61, 65] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 240 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row240_support i).mp hs)

#print axioms row240_support
#print axioms row240_source_zero
theorem row243_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 243 ↔
      i.val ∈ ([59, 60] : List Nat) := by
  revert i
  decide

theorem row243_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([59, 60] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 243 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row243_support i).mp hs)

#print axioms row243_support
#print axioms row243_source_zero
end AspisV8R19.R800SelectedSupportChunk14
