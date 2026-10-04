import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk32
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row503_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 503 ↔
      i.val ∈ ([128, 129] : List Nat) := by
  revert i
  decide

theorem row503_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([128, 129] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 503 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row503_support i).mp hs)

#print axioms row503_support
#print axioms row503_source_zero
theorem row505_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 505 ↔
      i.val ∈ ([129, 130, 131, 133] : List Nat) := by
  revert i
  decide

theorem row505_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([129, 130, 131, 133] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 505 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row505_support i).mp hs)

#print axioms row505_support
#print axioms row505_source_zero
theorem row507_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 507 ↔
      i.val ∈ ([130, 131] : List Nat) := by
  revert i
  decide

theorem row507_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([130, 131] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 507 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row507_support i).mp hs)

#print axioms row507_support
#print axioms row507_source_zero
theorem row509_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 509 ↔
      i.val ∈ ([131, 132, 133] : List Nat) := by
  revert i
  decide

theorem row509_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([131, 132, 133] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 509 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row509_support i).mp hs)

#print axioms row509_support
#print axioms row509_source_zero
end AspisV8R19.R800SelectedSupportChunk32
