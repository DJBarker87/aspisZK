import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk47
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row972_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 972 ↔
      i.val ∈ ([187, 188, 189, 190] : List Nat) := by
  revert i
  decide

theorem row972_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([187, 188, 189, 190] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 972 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row972_support i).mp hs)

#print axioms row972_support
#print axioms row972_source_zero
theorem row974_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 974 ↔
      i.val ∈ ([189, 190] : List Nat) := by
  revert i
  decide

theorem row974_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([189, 190] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 974 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row974_support i).mp hs)

#print axioms row974_support
#print axioms row974_source_zero
theorem row976_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 976 ↔
      i.val ∈ ([189, 190, 191, 192, 193, 194, 197, 198] : List Nat) := by
  revert i
  decide

theorem row976_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([189, 190, 191, 192, 193, 194, 197, 198] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 976 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row976_support i).mp hs)

#print axioms row976_support
#print axioms row976_source_zero
theorem row978_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 978 ↔
      i.val ∈ ([191, 192] : List Nat) := by
  revert i
  decide

theorem row978_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([191, 192] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 978 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row978_support i).mp hs)

#print axioms row978_support
#print axioms row978_source_zero
end AspisV8R19.R800SelectedSupportChunk47
