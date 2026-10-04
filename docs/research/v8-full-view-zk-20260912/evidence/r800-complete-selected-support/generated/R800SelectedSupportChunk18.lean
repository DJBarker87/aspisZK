import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk18
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row271_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 271 ↔
      i.val ∈ ([72, 73] : List Nat) := by
  revert i
  decide

theorem row271_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([72, 73] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 271 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row271_support i).mp hs)

#print axioms row271_support
#print axioms row271_source_zero
theorem row273_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 273 ↔
      i.val ∈ ([73, 74, 75, 77, 81] : List Nat) := by
  revert i
  decide

theorem row273_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([73, 74, 75, 77, 81] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 273 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row273_support i).mp hs)

#print axioms row273_support
#print axioms row273_source_zero
theorem row275_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 275 ↔
      i.val ∈ ([74, 75] : List Nat) := by
  revert i
  decide

theorem row275_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([74, 75] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 275 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row275_support i).mp hs)

#print axioms row275_support
#print axioms row275_source_zero
theorem row277_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 277 ↔
      i.val ∈ ([75, 76, 77] : List Nat) := by
  revert i
  decide

theorem row277_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([75, 76, 77] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 277 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row277_support i).mp hs)

#print axioms row277_support
#print axioms row277_source_zero
end AspisV8R19.R800SelectedSupportChunk18
