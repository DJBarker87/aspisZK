import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk13
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row228_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 228 ↔
      i.val ∈ ([51, 52, 53, 54] : List Nat) := by
  revert i
  decide

theorem row228_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([51, 52, 53, 54] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 228 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row228_support i).mp hs)

#print axioms row228_support
#print axioms row228_source_zero
theorem row230_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 230 ↔
      i.val ∈ ([53, 54] : List Nat) := by
  revert i
  decide

theorem row230_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([53, 54] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 230 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row230_support i).mp hs)

#print axioms row230_support
#print axioms row230_source_zero
theorem row232_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 232 ↔
      i.val ∈ ([53, 54, 55, 56, 57, 58] : List Nat) := by
  revert i
  decide

theorem row232_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([53, 54, 55, 56, 57, 58] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 232 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row232_support i).mp hs)

#print axioms row232_support
#print axioms row232_source_zero
theorem row234_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 234 ↔
      i.val ∈ ([55, 56] : List Nat) := by
  revert i
  decide

theorem row234_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([55, 56] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 234 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row234_support i).mp hs)

#print axioms row234_support
#print axioms row234_source_zero
end AspisV8R19.R800SelectedSupportChunk13
