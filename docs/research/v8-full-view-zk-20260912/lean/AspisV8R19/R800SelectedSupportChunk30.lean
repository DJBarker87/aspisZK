import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk30
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row372_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 372 ↔
      i.val ∈ ([120, 121, 122] : List Nat) := by
  revert i
  decide

theorem row372_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([120, 121, 122] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 372 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row372_support i).mp hs)

#print axioms row372_support
#print axioms row372_source_zero
theorem row374_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 374 ↔
      i.val ∈ ([121, 122] : List Nat) := by
  revert i
  decide

theorem row374_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([121, 122] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 374 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row374_support i).mp hs)

#print axioms row374_support
#print axioms row374_source_zero
theorem row376_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 376 ↔
      i.val ∈ ([121, 122, 123, 124, 125, 126] : List Nat) := by
  revert i
  decide

theorem row376_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([121, 122, 123, 124, 125, 126] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 376 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row376_support i).mp hs)

#print axioms row376_support
#print axioms row376_source_zero
theorem row378_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 378 ↔
      i.val ∈ ([123, 124] : List Nat) := by
  revert i
  decide

theorem row378_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([123, 124] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 378 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row378_support i).mp hs)

#print axioms row378_support
#print axioms row378_source_zero
end AspisV8R19.R800SelectedSupportChunk30
