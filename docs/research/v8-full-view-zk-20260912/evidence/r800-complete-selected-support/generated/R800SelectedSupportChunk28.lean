import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk28
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row353_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 353 ↔
      i.val ∈ ([112, 113, 114, 116, 119] : List Nat) := by
  revert i
  decide

theorem row353_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([112, 113, 114, 116, 119] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 353 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row353_support i).mp hs)

#print axioms row353_support
#print axioms row353_source_zero
theorem row355_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 355 ↔
      i.val ∈ ([113, 114] : List Nat) := by
  revert i
  decide

theorem row355_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([113, 114] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 355 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row355_support i).mp hs)

#print axioms row355_support
#print axioms row355_source_zero
theorem row357_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 357 ↔
      i.val ∈ ([114, 115, 116] : List Nat) := by
  revert i
  decide

theorem row357_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([114, 115, 116] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 357 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row357_support i).mp hs)

#print axioms row357_support
#print axioms row357_source_zero
theorem row359_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 359 ↔
      i.val ∈ ([115, 116] : List Nat) := by
  revert i
  decide

theorem row359_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([115, 116] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 359 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row359_support i).mp hs)

#print axioms row359_support
#print axioms row359_source_zero
end AspisV8R19.R800SelectedSupportChunk28
