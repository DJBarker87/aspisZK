import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk52
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row1013_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1013 ↔
      i.val ∈ ([208, 209, 210] : List Nat) := by
  revert i
  decide

theorem row1013_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([208, 209, 210] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1013 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1013_support i).mp hs)

#print axioms row1013_support
#print axioms row1013_source_zero
theorem row1015_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1015 ↔
      i.val ∈ ([209, 210] : List Nat) := by
  revert i
  decide

theorem row1015_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([209, 210] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1015 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1015_support i).mp hs)

#print axioms row1015_support
#print axioms row1015_source_zero
theorem row1017_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1017 ↔
      i.val ∈ ([210, 211, 212, 213] : List Nat) := by
  revert i
  decide

theorem row1017_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([210, 211, 212, 213] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1017 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1017_support i).mp hs)

#print axioms row1017_support
#print axioms row1017_source_zero
theorem row1019_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 1019 ↔
      i.val ∈ ([211, 212, 213] : List Nat) := by
  revert i
  decide

theorem row1019_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([211, 212, 213] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 1019 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row1019_support i).mp hs)

#print axioms row1019_support
#print axioms row1019_source_zero
end AspisV8R19.R800SelectedSupportChunk52
