import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk35
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row639_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 639 ↔
      i.val ∈ ([139, 140, 141] : List Nat) := by
  revert i
  decide

theorem row639_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([139, 140, 141] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 639 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row639_support i).mp hs)

#print axioms row639_support
#print axioms row639_source_zero
theorem row755_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 755 ↔
      i.val ∈ ([142] : List Nat) := by
  revert i
  decide

theorem row755_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([142] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 755 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row755_support i).mp hs)

#print axioms row755_support
#print axioms row755_source_zero
theorem row757_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 757 ↔
      i.val ∈ ([142, 143, 144] : List Nat) := by
  revert i
  decide

theorem row757_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([142, 143, 144] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 757 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row757_support i).mp hs)

#print axioms row757_support
#print axioms row757_source_zero
theorem row759_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 759 ↔
      i.val ∈ ([143, 144] : List Nat) := by
  revert i
  decide

theorem row759_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([143, 144] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 759 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row759_support i).mp hs)

#print axioms row759_support
#print axioms row759_source_zero
end AspisV8R19.R800SelectedSupportChunk35
