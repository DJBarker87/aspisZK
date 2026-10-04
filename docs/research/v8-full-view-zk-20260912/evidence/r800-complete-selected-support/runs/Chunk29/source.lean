import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk29
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row361_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 361 ↔
      i.val ∈ ([116, 117, 119] : List Nat) := by
  revert i
  decide

theorem row361_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([116, 117, 119] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 361 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row361_support i).mp hs)

#print axioms row361_support
#print axioms row361_source_zero
theorem row365_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 365 ↔
      i.val ∈ ([118, 119] : List Nat) := by
  revert i
  decide

theorem row365_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([118, 119] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 365 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row365_support i).mp hs)

#print axioms row365_support
#print axioms row365_source_zero
theorem row367_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 367 ↔
      i.val ∈ ([118, 119] : List Nat) := by
  revert i
  decide

theorem row367_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([118, 119] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 367 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row367_support i).mp hs)

#print axioms row367_support
#print axioms row367_source_zero
theorem row370_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 370 ↔
      i.val ∈ ([119, 120] : List Nat) := by
  revert i
  decide

theorem row370_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([119, 120] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 370 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row370_support i).mp hs)

#print axioms row370_support
#print axioms row370_source_zero
end AspisV8R19.R800SelectedSupportChunk29
