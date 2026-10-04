import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk45
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row954_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 954 ↔
      i.val ∈ ([180, 181] : List Nat) := by
  revert i
  decide

theorem row954_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([180, 181] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 954 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row954_support i).mp hs)

#print axioms row954_support
#print axioms row954_source_zero
theorem row958_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 958 ↔
      i.val ∈ ([182] : List Nat) := by
  revert i
  decide

theorem row958_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([182] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 958 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row958_support i).mp hs)

#print axioms row958_support
#print axioms row958_source_zero
theorem row960_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 960 ↔
      i.val ∈ ([182, 183, 184, 185, 186, 189, 190, 197, 198] : List Nat) := by
  revert i
  decide

theorem row960_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([182, 183, 184, 185, 186, 189, 190, 197, 198] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 960 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row960_support i).mp hs)

#print axioms row960_support
#print axioms row960_source_zero
theorem row962_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 962 ↔
      i.val ∈ ([183, 184] : List Nat) := by
  revert i
  decide

theorem row962_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([183, 184] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 962 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row962_support i).mp hs)

#print axioms row962_support
#print axioms row962_source_zero
end AspisV8R19.R800SelectedSupportChunk45
