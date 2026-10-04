import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk12
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row220_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 220 ↔
      i.val ∈ ([47, 48, 49, 50] : List Nat) := by
  revert i
  decide

theorem row220_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([47, 48, 49, 50] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 220 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row220_support i).mp hs)

#print axioms row220_support
#print axioms row220_source_zero
theorem row222_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 222 ↔
      i.val ∈ ([49, 50] : List Nat) := by
  revert i
  decide

theorem row222_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([49, 50] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 222 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row222_support i).mp hs)

#print axioms row222_support
#print axioms row222_source_zero
theorem row224_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 224 ↔
      i.val ∈ ([49, 50, 51, 52, 53, 54, 57, 58, 65] : List Nat) := by
  revert i
  decide

theorem row224_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([49, 50, 51, 52, 53, 54, 57, 58, 65] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 224 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row224_support i).mp hs)

#print axioms row224_support
#print axioms row224_source_zero
theorem row226_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 226 ↔
      i.val ∈ ([51, 52] : List Nat) := by
  revert i
  decide

theorem row226_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([51, 52] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 226 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row226_support i).mp hs)

#print axioms row226_support
#print axioms row226_source_zero
end AspisV8R19.R800SelectedSupportChunk12
