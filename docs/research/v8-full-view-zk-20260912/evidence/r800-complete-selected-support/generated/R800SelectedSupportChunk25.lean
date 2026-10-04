import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk25
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row329_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 329 ↔
      i.val ∈ ([100, 101, 102, 104] : List Nat) := by
  revert i
  decide

theorem row329_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([100, 101, 102, 104] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 329 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row329_support i).mp hs)

#print axioms row329_support
#print axioms row329_source_zero
theorem row331_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 331 ↔
      i.val ∈ ([101, 102] : List Nat) := by
  revert i
  decide

theorem row331_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([101, 102] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 331 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row331_support i).mp hs)

#print axioms row331_support
#print axioms row331_source_zero
theorem row333_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 333 ↔
      i.val ∈ ([102, 103, 104] : List Nat) := by
  revert i
  decide

theorem row333_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([102, 103, 104] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 333 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row333_support i).mp hs)

#print axioms row333_support
#print axioms row333_source_zero
theorem row335_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 335 ↔
      i.val ∈ ([103, 104] : List Nat) := by
  revert i
  decide

theorem row335_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([103, 104] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 335 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row335_support i).mp hs)

#print axioms row335_support
#print axioms row335_source_zero
end AspisV8R19.R800SelectedSupportChunk25
