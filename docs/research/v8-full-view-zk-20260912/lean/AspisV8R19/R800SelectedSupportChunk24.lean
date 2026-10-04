import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk24
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row321_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 321 ↔
      i.val ∈ ([96, 97, 98, 100, 104, 112] : List Nat) := by
  revert i
  decide

theorem row321_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([96, 97, 98, 100, 104, 112] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 321 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row321_support i).mp hs)

#print axioms row321_support
#print axioms row321_source_zero
theorem row323_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 323 ↔
      i.val ∈ ([97, 98] : List Nat) := by
  revert i
  decide

theorem row323_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([97, 98] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 323 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row323_support i).mp hs)

#print axioms row323_support
#print axioms row323_source_zero
theorem row325_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 325 ↔
      i.val ∈ ([98, 99, 100] : List Nat) := by
  revert i
  decide

theorem row325_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([98, 99, 100] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 325 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row325_support i).mp hs)

#print axioms row325_support
#print axioms row325_source_zero
theorem row327_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 327 ↔
      i.val ∈ ([99, 100] : List Nat) := by
  revert i
  decide

theorem row327_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([99, 100] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 327 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row327_support i).mp hs)

#print axioms row327_support
#print axioms row327_source_zero
end AspisV8R19.R800SelectedSupportChunk24
