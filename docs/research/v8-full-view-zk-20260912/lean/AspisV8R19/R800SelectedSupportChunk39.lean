import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk39
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row902_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 902 ↔
      i.val ∈ ([156, 157] : List Nat) := by
  revert i
  decide

theorem row902_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([156, 157] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 902 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row902_support i).mp hs)

#print axioms row902_support
#print axioms row902_source_zero
theorem row904_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 904 ↔
      i.val ∈ ([156, 157, 158, 159, 160, 161] : List Nat) := by
  revert i
  decide

theorem row904_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([156, 157, 158, 159, 160, 161] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 904 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row904_support i).mp hs)

#print axioms row904_support
#print axioms row904_source_zero
theorem row906_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 906 ↔
      i.val ∈ ([158, 159] : List Nat) := by
  revert i
  decide

theorem row906_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([158, 159] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 906 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row906_support i).mp hs)

#print axioms row906_support
#print axioms row906_source_zero
theorem row908_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 908 ↔
      i.val ∈ ([158, 159, 160, 161] : List Nat) := by
  revert i
  decide

theorem row908_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([158, 159, 160, 161] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 908 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row908_support i).mp hs)

#print axioms row908_support
#print axioms row908_source_zero
end AspisV8R19.R800SelectedSupportChunk39
