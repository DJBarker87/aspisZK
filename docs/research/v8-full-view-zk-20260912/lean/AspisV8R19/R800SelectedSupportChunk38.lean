import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk38
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row890_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 890 ↔
      i.val ∈ ([152, 153] : List Nat) := by
  revert i
  decide

theorem row890_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([152, 153] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 890 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row890_support i).mp hs)

#print axioms row890_support
#print axioms row890_source_zero
theorem row892_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 892 ↔
      i.val ∈ ([152, 153, 154, 155] : List Nat) := by
  revert i
  decide

theorem row892_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([152, 153, 154, 155] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 892 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row892_support i).mp hs)

#print axioms row892_support
#print axioms row892_source_zero
theorem row894_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 894 ↔
      i.val ∈ ([154, 155] : List Nat) := by
  revert i
  decide

theorem row894_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([154, 155] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 894 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row894_support i).mp hs)

#print axioms row894_support
#print axioms row894_source_zero
theorem row900_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 900 ↔
      i.val ∈ ([156, 157] : List Nat) := by
  revert i
  decide

theorem row900_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([156, 157] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 900 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row900_support i).mp hs)

#print axioms row900_support
#print axioms row900_source_zero
end AspisV8R19.R800SelectedSupportChunk38
