import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk20
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row287_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 287 ↔
      i.val ∈ ([80, 81] : List Nat) := by
  revert i
  decide

theorem row287_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([80, 81] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 287 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row287_support i).mp hs)

#print axioms row287_support
#print axioms row287_source_zero
theorem row289_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 289 ↔
      i.val ∈ ([81, 82, 83, 85, 89, 96] : List Nat) := by
  revert i
  decide

theorem row289_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([81, 82, 83, 85, 89, 96] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 289 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row289_support i).mp hs)

#print axioms row289_support
#print axioms row289_source_zero
theorem row291_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 291 ↔
      i.val ∈ ([82, 83] : List Nat) := by
  revert i
  decide

theorem row291_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([82, 83] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 291 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row291_support i).mp hs)

#print axioms row291_support
#print axioms row291_source_zero
theorem row293_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 293 ↔
      i.val ∈ ([83, 84, 85] : List Nat) := by
  revert i
  decide

theorem row293_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([83, 84, 85] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 293 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row293_support i).mp hs)

#print axioms row293_support
#print axioms row293_source_zero
end AspisV8R19.R800SelectedSupportChunk20
