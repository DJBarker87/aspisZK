import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk50
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row996_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 996 ↔
      i.val ∈ ([199, 200, 201, 202] : List Nat) := by
  revert i
  decide

theorem row996_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([199, 200, 201, 202] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 996 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row996_support i).mp hs)

#print axioms row996_support
#print axioms row996_source_zero
theorem row998_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 998 ↔
      i.val ∈ ([201, 202] : List Nat) := by
  revert i
  decide

theorem row998_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([201, 202] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 998 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row998_support i).mp hs)

#print axioms row998_support
#print axioms row998_source_zero
theorem row1000_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1000 ↔
      i.val ∈ ([201, 202, 203, 204, 205, 206] : List Nat) := by
  revert i
  decide

theorem row1000_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([201, 202, 203, 204, 205, 206] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1000 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1000_support i).mp hs)

#print axioms row1000_support
#print axioms row1000_source_zero
theorem row1002_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1002 ↔
      i.val ∈ ([203, 204] : List Nat) := by
  revert i
  decide

theorem row1002_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([203, 204] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1002 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1002_support i).mp hs)

#print axioms row1002_support
#print axioms row1002_source_zero
end AspisV8R19.R800SelectedSupportChunk50
