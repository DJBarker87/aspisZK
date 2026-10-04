import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk36
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row761_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 761 ↔
      i.val ∈ ([144, 145, 146] : List Nat) := by
  revert i
  decide

theorem row761_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([144, 145, 146] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 761 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row761_support i).mp hs)

#print axioms row761_support
#print axioms row761_source_zero
theorem row763_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 763 ↔
      i.val ∈ ([145, 146] : List Nat) := by
  revert i
  decide

theorem row763_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([145, 146] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 763 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row763_support i).mp hs)

#print axioms row763_support
#print axioms row763_source_zero
theorem row765_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 765 ↔
      i.val ∈ ([146, 147, 148] : List Nat) := by
  revert i
  decide

theorem row765_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([146, 147, 148] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 765 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row765_support i).mp hs)

#print axioms row765_support
#print axioms row765_source_zero
theorem row766_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 766 ↔
      i.val ∈ ([146, 147, 148] : List Nat) := by
  revert i
  decide

theorem row766_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([146, 147, 148] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 766 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row766_support i).mp hs)

#print axioms row766_support
#print axioms row766_source_zero
end AspisV8R19.R800SelectedSupportChunk36
