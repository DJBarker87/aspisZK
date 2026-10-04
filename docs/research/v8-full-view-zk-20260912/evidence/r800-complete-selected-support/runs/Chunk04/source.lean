import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk04
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row148_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 148 ↔
      i.val ∈ ([15, 16, 17, 18] : List Nat) := by
  revert i
  decide

theorem row148_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([15, 16, 17, 18] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 148 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row148_support i).mp hs)

#print axioms row148_support
#print axioms row148_source_zero
theorem row150_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 150 ↔
      i.val ∈ ([17, 18] : List Nat) := by
  revert i
  decide

theorem row150_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([17, 18] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 150 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row150_support i).mp hs)

#print axioms row150_support
#print axioms row150_source_zero
theorem row152_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 152 ↔
      i.val ∈ ([17, 18, 19, 20, 21, 22] : List Nat) := by
  revert i
  decide

theorem row152_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([17, 18, 19, 20, 21, 22] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 152 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row152_support i).mp hs)

#print axioms row152_support
#print axioms row152_source_zero
theorem row154_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 154 ↔
      i.val ∈ ([19, 20] : List Nat) := by
  revert i
  decide

theorem row154_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([19, 20] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 154 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row154_support i).mp hs)

#print axioms row154_support
#print axioms row154_source_zero
end AspisV8R19.R800SelectedSupportChunk04
