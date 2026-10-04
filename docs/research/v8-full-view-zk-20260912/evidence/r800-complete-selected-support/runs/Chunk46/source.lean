import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk46
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row964_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 964 ↔
      i.val ∈ ([183, 184, 185, 186] : List Nat) := by
  revert i
  decide

theorem row964_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([183, 184, 185, 186] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 964 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row964_support i).mp hs)

#print axioms row964_support
#print axioms row964_source_zero
theorem row966_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 966 ↔
      i.val ∈ ([185, 186] : List Nat) := by
  revert i
  decide

theorem row966_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([185, 186] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 966 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row966_support i).mp hs)

#print axioms row966_support
#print axioms row966_source_zero
theorem row968_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 968 ↔
      i.val ∈ ([185, 186, 187, 188, 189, 190] : List Nat) := by
  revert i
  decide

theorem row968_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([185, 186, 187, 188, 189, 190] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 968 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row968_support i).mp hs)

#print axioms row968_support
#print axioms row968_source_zero
theorem row970_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 970 ↔
      i.val ∈ ([187, 188] : List Nat) := by
  revert i
  decide

theorem row970_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([187, 188] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 970 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row970_support i).mp hs)

#print axioms row970_support
#print axioms row970_source_zero
end AspisV8R19.R800SelectedSupportChunk46
