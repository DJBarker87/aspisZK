import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk41
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row918_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 918 ↔
      i.val ∈ ([164, 165] : List Nat) := by
  revert i
  decide

theorem row918_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([164, 165] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 918 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row918_support i).mp hs)

#print axioms row918_support
#print axioms row918_source_zero
theorem row920_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 920 ↔
      i.val ∈ ([164, 165, 166, 167, 168, 169] : List Nat) := by
  revert i
  decide

theorem row920_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([164, 165, 166, 167, 168, 169] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 920 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row920_support i).mp hs)

#print axioms row920_support
#print axioms row920_source_zero
theorem row922_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 922 ↔
      i.val ∈ ([166, 167] : List Nat) := by
  revert i
  decide

theorem row922_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([166, 167] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 922 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row922_support i).mp hs)

#print axioms row922_support
#print axioms row922_source_zero
theorem row924_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 924 ↔
      i.val ∈ ([166, 167, 168, 169] : List Nat) := by
  revert i
  decide

theorem row924_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([166, 167, 168, 169] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 924 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row924_support i).mp hs)

#print axioms row924_support
#print axioms row924_source_zero
end AspisV8R19.R800SelectedSupportChunk41
