import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk23
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row313_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 313 ↔
      i.val ∈ ([92, 93, 94, 96] : List Nat) := by
  revert i
  decide

theorem row313_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([92, 93, 94, 96] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 313 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row313_support i).mp hs)

#print axioms row313_support
#print axioms row313_source_zero
theorem row315_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 315 ↔
      i.val ∈ ([93, 94] : List Nat) := by
  revert i
  decide

theorem row315_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([93, 94] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 315 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row315_support i).mp hs)

#print axioms row315_support
#print axioms row315_source_zero
theorem row317_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 317 ↔
      i.val ∈ ([94, 95, 96] : List Nat) := by
  revert i
  decide

theorem row317_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([94, 95, 96] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 317 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row317_support i).mp hs)

#print axioms row317_support
#print axioms row317_source_zero
theorem row319_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 319 ↔
      i.val ∈ ([95, 96] : List Nat) := by
  revert i
  decide

theorem row319_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([95, 96] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 319 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row319_support i).mp hs)

#print axioms row319_support
#print axioms row319_source_zero
end AspisV8R19.R800SelectedSupportChunk23
