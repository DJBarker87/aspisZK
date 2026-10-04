import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk00
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row116_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 116 ↔
      i.val ∈ ([0, 1, 2] : List Nat) := by
  revert i
  decide

theorem row116_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([0, 1, 2] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 116 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row116_support i).mp hs)

#print axioms row116_support
#print axioms row116_source_zero
theorem row118_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 118 ↔
      i.val ∈ ([1, 2] : List Nat) := by
  revert i
  decide

theorem row118_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([1, 2] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 118 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row118_support i).mp hs)

#print axioms row118_support
#print axioms row118_source_zero
theorem row120_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 120 ↔
      i.val ∈ ([1, 2, 3, 4, 5, 6] : List Nat) := by
  revert i
  decide

theorem row120_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([1, 2, 3, 4, 5, 6] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 120 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row120_support i).mp hs)

#print axioms row120_support
#print axioms row120_source_zero
theorem row122_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 122 ↔
      i.val ∈ ([3, 4] : List Nat) := by
  revert i
  decide

theorem row122_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([3, 4] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 122 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row122_support i).mp hs)

#print axioms row122_support
#print axioms row122_source_zero
end AspisV8R19.R800SelectedSupportChunk00
