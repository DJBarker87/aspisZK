import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk15
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row245_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 245 ↔
      i.val ∈ ([60, 61, 62] : List Nat) := by
  revert i
  decide

theorem row245_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([60, 61, 62] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 245 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row245_support i).mp hs)

#print axioms row245_support
#print axioms row245_source_zero
theorem row247_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 247 ↔
      i.val ∈ ([61, 62] : List Nat) := by
  revert i
  decide

theorem row247_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([61, 62] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 247 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row247_support i).mp hs)

#print axioms row247_support
#print axioms row247_source_zero
theorem row249_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 249 ↔
      i.val ∈ ([62, 63, 64] : List Nat) := by
  revert i
  decide

theorem row249_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([62, 63, 64] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 249 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row249_support i).mp hs)

#print axioms row249_support
#print axioms row249_source_zero
theorem row251_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 251 ↔
      i.val ∈ ([63, 64] : List Nat) := by
  revert i
  decide

theorem row251_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([63, 64] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 251 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row251_support i).mp hs)

#print axioms row251_support
#print axioms row251_source_zero
end AspisV8R19.R800SelectedSupportChunk15
