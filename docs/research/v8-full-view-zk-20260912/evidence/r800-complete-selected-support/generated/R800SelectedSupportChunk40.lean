import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk40
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row910_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 910 ↔
      i.val ∈ ([160, 161] : List Nat) := by
  revert i
  decide

theorem row910_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([160, 161] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 910 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row910_support i).mp hs)

#print axioms row910_support
#print axioms row910_source_zero
theorem row912_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 912 ↔
      i.val ∈ ([160, 161, 162, 163, 164, 165, 168, 169] : List Nat) := by
  revert i
  decide

theorem row912_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([160, 161, 162, 163, 164, 165, 168, 169] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 912 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row912_support i).mp hs)

#print axioms row912_support
#print axioms row912_source_zero
theorem row914_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 914 ↔
      i.val ∈ ([162, 163] : List Nat) := by
  revert i
  decide

theorem row914_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([162, 163] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 914 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row914_support i).mp hs)

#print axioms row914_support
#print axioms row914_source_zero
theorem row916_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 916 ↔
      i.val ∈ ([162, 163, 164, 165] : List Nat) := by
  revert i
  decide

theorem row916_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([162, 163, 164, 165] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 916 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row916_support i).mp hs)

#print axioms row916_support
#print axioms row916_source_zero
end AspisV8R19.R800SelectedSupportChunk40
