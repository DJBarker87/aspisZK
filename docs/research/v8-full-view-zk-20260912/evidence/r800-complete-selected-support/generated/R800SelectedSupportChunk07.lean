import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk07
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row172_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 172 ↔
      i.val ∈ ([27, 28, 29, 30] : List Nat) := by
  revert i
  decide

theorem row172_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([27, 28, 29, 30] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 172 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row172_support i).mp hs)

#print axioms row172_support
#print axioms row172_source_zero
theorem row174_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 174 ↔
      i.val ∈ ([29, 30] : List Nat) := by
  revert i
  decide

theorem row174_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([29, 30] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 174 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row174_support i).mp hs)

#print axioms row174_support
#print axioms row174_source_zero
theorem row176_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 176 ↔
      i.val ∈ ([29, 30, 31, 32, 33, 35] : List Nat) := by
  revert i
  decide

theorem row176_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([29, 30, 31, 32, 33, 35] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 176 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row176_support i).mp hs)

#print axioms row176_support
#print axioms row176_source_zero
theorem row178_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 178 ↔
      i.val ∈ ([31, 32, 221] : List Nat) := by
  revert i
  decide

theorem row178_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([31, 32, 221] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 178 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row178_support i).mp hs)

#print axioms row178_support
#print axioms row178_source_zero
end AspisV8R19.R800SelectedSupportChunk07
