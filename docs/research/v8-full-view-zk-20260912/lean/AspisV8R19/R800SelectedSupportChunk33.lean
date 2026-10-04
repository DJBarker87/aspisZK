import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk33
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row511_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 511 ↔
      i.val ∈ ([132, 133] : List Nat) := by
  revert i
  decide

theorem row511_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([132, 133] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 511 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row511_support i).mp hs)

#print axioms row511_support
#print axioms row511_source_zero
theorem row626_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 626 ↔
      i.val ∈ ([134, 141] : List Nat) := by
  revert i
  decide

theorem row626_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([134, 141] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 626 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row626_support i).mp hs)

#print axioms row626_support
#print axioms row626_source_zero
theorem row628_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 628 ↔
      i.val ∈ ([134, 135, 136] : List Nat) := by
  revert i
  decide

theorem row628_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([134, 135, 136] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 628 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row628_support i).mp hs)

#print axioms row628_support
#print axioms row628_source_zero
theorem row630_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 630 ↔
      i.val ∈ ([135, 136] : List Nat) := by
  revert i
  decide

theorem row630_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([135, 136] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 630 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row630_support i).mp hs)

#print axioms row630_support
#print axioms row630_source_zero
end AspisV8R19.R800SelectedSupportChunk33
