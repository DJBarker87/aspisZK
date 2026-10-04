import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk44
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row942_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 942 ↔
      i.val ∈ ([176, 177] : List Nat) := by
  revert i
  decide

theorem row942_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([176, 177] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 942 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row942_support i).mp hs)

#print axioms row942_support
#print axioms row942_source_zero
theorem row944_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 944 ↔
      i.val ∈ ([176, 177, 178, 179, 182] : List Nat) := by
  revert i
  decide

theorem row944_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([176, 177, 178, 179, 182] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 944 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row944_support i).mp hs)

#print axioms row944_support
#print axioms row944_source_zero
theorem row948_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 948 ↔
      i.val ∈ ([178, 179] : List Nat) := by
  revert i
  decide

theorem row948_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([178, 179] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 948 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row948_support i).mp hs)

#print axioms row948_support
#print axioms row948_source_zero
theorem row952_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 952 ↔
      i.val ∈ ([179, 180, 181, 182] : List Nat) := by
  revert i
  decide

theorem row952_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([179, 180, 181, 182] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 952 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row952_support i).mp hs)

#print axioms row952_support
#print axioms row952_source_zero
end AspisV8R19.R800SelectedSupportChunk44
