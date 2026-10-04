import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk51
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row1004_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1004 ↔
      i.val ∈ ([203, 204, 205, 206] : List Nat) := by
  revert i
  decide

theorem row1004_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([203, 204, 205, 206] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1004 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1004_support i).mp hs)

#print axioms row1004_support
#print axioms row1004_source_zero
theorem row1006_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1006 ↔
      i.val ∈ ([205, 206] : List Nat) := by
  revert i
  decide

theorem row1006_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([205, 206] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1006 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1006_support i).mp hs)

#print axioms row1006_support
#print axioms row1006_source_zero
theorem row1008_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1008 ↔
      i.val ∈ ([205, 206, 207, 208, 209] : List Nat) := by
  revert i
  decide

theorem row1008_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([205, 206, 207, 208, 209] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1008 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1008_support i).mp hs)

#print axioms row1008_support
#print axioms row1008_source_zero
theorem row1011_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1011 ↔
      i.val ∈ ([207, 208] : List Nat) := by
  revert i
  decide

theorem row1011_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([207, 208] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1011 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1011_support i).mp hs)

#print axioms row1011_support
#print axioms row1011_source_zero
end AspisV8R19.R800SelectedSupportChunk51
