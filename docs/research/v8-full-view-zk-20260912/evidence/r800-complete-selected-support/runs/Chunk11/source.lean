import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk11
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row212_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 212 ↔
      i.val ∈ ([43, 44, 45, 46] : List Nat) := by
  revert i
  decide

theorem row212_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([43, 44, 45, 46] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 212 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row212_support i).mp hs)

#print axioms row212_support
#print axioms row212_source_zero
theorem row214_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 214 ↔
      i.val ∈ ([45, 46] : List Nat) := by
  revert i
  decide

theorem row214_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([45, 46] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 214 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row214_support i).mp hs)

#print axioms row214_support
#print axioms row214_source_zero
theorem row216_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 216 ↔
      i.val ∈ ([45, 46, 47, 48, 49, 50] : List Nat) := by
  revert i
  decide

theorem row216_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([45, 46, 47, 48, 49, 50] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 216 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row216_support i).mp hs)

#print axioms row216_support
#print axioms row216_source_zero
theorem row218_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 218 ↔
      i.val ∈ ([47, 48] : List Nat) := by
  revert i
  decide

theorem row218_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([47, 48] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 218 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row218_support i).mp hs)

#print axioms row218_support
#print axioms row218_source_zero
end AspisV8R19.R800SelectedSupportChunk11
