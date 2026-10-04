import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk26
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row337_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 337 ↔
      i.val ∈ ([104, 105, 106, 108, 112] : List Nat) := by
  revert i
  decide

theorem row337_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([104, 105, 106, 108, 112] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 337 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row337_support i).mp hs)

#print axioms row337_support
#print axioms row337_source_zero
theorem row339_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 339 ↔
      i.val ∈ ([105, 106] : List Nat) := by
  revert i
  decide

theorem row339_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([105, 106] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 339 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row339_support i).mp hs)

#print axioms row339_support
#print axioms row339_source_zero
theorem row341_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 341 ↔
      i.val ∈ ([106, 107, 108] : List Nat) := by
  revert i
  decide

theorem row341_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([106, 107, 108] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 341 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row341_support i).mp hs)

#print axioms row341_support
#print axioms row341_source_zero
theorem row343_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 343 ↔
      i.val ∈ ([107, 108] : List Nat) := by
  revert i
  decide

theorem row343_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([107, 108] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 343 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row343_support i).mp hs)

#print axioms row343_support
#print axioms row343_source_zero
end AspisV8R19.R800SelectedSupportChunk26
