import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk22
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row303_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 303 ↔
      i.val ∈ ([88, 89] : List Nat) := by
  revert i
  decide

theorem row303_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([88, 89] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 303 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row303_support i).mp hs)

#print axioms row303_support
#print axioms row303_source_zero
theorem row305_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 305 ↔
      i.val ∈ ([89, 90, 91, 92, 96] : List Nat) := by
  revert i
  decide

theorem row305_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([89, 90, 91, 92, 96] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 305 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row305_support i).mp hs)

#print axioms row305_support
#print axioms row305_source_zero
theorem row307_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 307 ↔
      i.val ∈ ([90, 91] : List Nat) := by
  revert i
  decide

theorem row307_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([90, 91] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 307 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row307_support i).mp hs)

#print axioms row307_support
#print axioms row307_source_zero
theorem row311_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 311 ↔
      i.val ∈ ([92] : List Nat) := by
  revert i
  decide

theorem row311_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([92] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 311 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row311_support i).mp hs)

#print axioms row311_support
#print axioms row311_source_zero
end AspisV8R19.R800SelectedSupportChunk22
