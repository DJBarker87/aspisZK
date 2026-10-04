import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk48
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row980_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 980 ↔
      i.val ∈ ([191, 192, 193, 194] : List Nat) := by
  revert i
  decide

theorem row980_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([191, 192, 193, 194] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 980 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row980_support i).mp hs)

#print axioms row980_support
#print axioms row980_source_zero
theorem row982_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 982 ↔
      i.val ∈ ([193, 194] : List Nat) := by
  revert i
  decide

theorem row982_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([193, 194] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 982 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row982_support i).mp hs)

#print axioms row982_support
#print axioms row982_source_zero
theorem row984_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 984 ↔
      i.val ∈ ([193, 194, 195, 196, 197, 198] : List Nat) := by
  revert i
  decide

theorem row984_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([193, 194, 195, 196, 197, 198] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 984 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row984_support i).mp hs)

#print axioms row984_support
#print axioms row984_source_zero
theorem row986_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 986 ↔
      i.val ∈ ([195, 196] : List Nat) := by
  revert i
  decide

theorem row986_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([195, 196] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 986 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row986_support i).mp hs)

#print axioms row986_support
#print axioms row986_source_zero
end AspisV8R19.R800SelectedSupportChunk48
