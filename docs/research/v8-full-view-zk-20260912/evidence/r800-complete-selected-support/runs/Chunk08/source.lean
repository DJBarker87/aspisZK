import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk08
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row180_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 180 ↔
      i.val ∈ ([31, 32, 33] : List Nat) := by
  revert i
  decide

theorem row180_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([31, 32, 33] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 180 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row180_support i).mp hs)

#print axioms row180_support
#print axioms row180_source_zero
theorem row184_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 184 ↔
      i.val ∈ ([33, 34, 35] : List Nat) := by
  revert i
  decide

theorem row184_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([33, 34, 35] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 184 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row184_support i).mp hs)

#print axioms row184_support
#print axioms row184_source_zero
theorem row190_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 190 ↔
      i.val ∈ ([35, 221] : List Nat) := by
  revert i
  decide

theorem row190_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([35, 221] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 190 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row190_support i).mp hs)

#print axioms row190_support
#print axioms row190_source_zero
theorem row194_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 194 ↔
      i.val ∈ ([36, 221] : List Nat) := by
  revert i
  decide

theorem row194_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([36, 221] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 194 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row194_support i).mp hs)

#print axioms row194_support
#print axioms row194_source_zero
end AspisV8R19.R800SelectedSupportChunk08
