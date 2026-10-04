import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk42
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row926_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 926 ↔
      i.val ∈ ([168, 169] : List Nat) := by
  revert i
  decide

theorem row926_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([168, 169] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 926 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row926_support i).mp hs)

#print axioms row926_support
#print axioms row926_source_zero
theorem row928_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 928 ↔
      i.val ∈ ([168, 169, 170, 171, 172, 173, 176, 177, 182] : List Nat) := by
  revert i
  decide

theorem row928_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([168, 169, 170, 171, 172, 173, 176, 177, 182] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 928 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row928_support i).mp hs)

#print axioms row928_support
#print axioms row928_source_zero
theorem row930_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 930 ↔
      i.val ∈ ([170, 171] : List Nat) := by
  revert i
  decide

theorem row930_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([170, 171] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 930 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row930_support i).mp hs)

#print axioms row930_support
#print axioms row930_source_zero
theorem row932_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 932 ↔
      i.val ∈ ([170, 171, 172, 173] : List Nat) := by
  revert i
  decide

theorem row932_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([170, 171, 172, 173] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 932 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row932_support i).mp hs)

#print axioms row932_support
#print axioms row932_source_zero
end AspisV8R19.R800SelectedSupportChunk42
