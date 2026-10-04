import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportPrototype
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

-- Each table checks 222 index pairs, ten bounded index-loop steps and no field arithmetic.
theorem row114_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 114 ↔
      i.val ∈ ([0,220] : List Nat) := by
  revert i
  decide

theorem row1022_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1022 ↔
      i.val ∈ ([212] : List Nat) := by
  revert i
  decide

variable {F : Type*} [CommRing F]
theorem row114_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([0,220] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 114 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row114_support i).mp hs)

theorem row1022_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([212] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1022 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1022_support i).mp hs)

#print axioms row114_support
#print axioms row1022_support
#print axioms row114_source_zero
#print axioms row1022_source_zero
end AspisV8R19.R800SelectedSupportPrototype
