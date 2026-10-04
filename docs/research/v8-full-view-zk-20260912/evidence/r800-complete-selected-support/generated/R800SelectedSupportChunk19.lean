import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk19
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row279_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 279 ↔
      i.val ∈ ([76, 77] : List Nat) := by
  revert i
  decide

theorem row279_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([76, 77] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 279 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row279_support i).mp hs)

#print axioms row279_support
#print axioms row279_source_zero
theorem row281_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 281 ↔
      i.val ∈ ([77, 78, 79, 81] : List Nat) := by
  revert i
  decide

theorem row281_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([77, 78, 79, 81] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 281 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row281_support i).mp hs)

#print axioms row281_support
#print axioms row281_source_zero
theorem row283_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 283 ↔
      i.val ∈ ([78, 79] : List Nat) := by
  revert i
  decide

theorem row283_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([78, 79] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 283 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row283_support i).mp hs)

#print axioms row283_support
#print axioms row283_source_zero
theorem row285_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 285 ↔
      i.val ∈ ([79, 80, 81] : List Nat) := by
  revert i
  decide

theorem row285_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([79, 80, 81] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 285 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row285_support i).mp hs)

#print axioms row285_support
#print axioms row285_source_zero
end AspisV8R19.R800SelectedSupportChunk19
