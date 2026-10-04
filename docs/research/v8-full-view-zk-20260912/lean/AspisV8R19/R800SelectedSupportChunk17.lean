import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk17
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row263_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 263 ↔
      i.val ∈ ([68, 69] : List Nat) := by
  revert i
  decide

theorem row263_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([68, 69] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 263 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row263_support i).mp hs)

#print axioms row263_support
#print axioms row263_source_zero
theorem row265_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 265 ↔
      i.val ∈ ([69, 70, 71, 73] : List Nat) := by
  revert i
  decide

theorem row265_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([69, 70, 71, 73] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 265 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row265_support i).mp hs)

#print axioms row265_support
#print axioms row265_source_zero
theorem row267_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 267 ↔
      i.val ∈ ([70, 71] : List Nat) := by
  revert i
  decide

theorem row267_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([70, 71] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 267 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row267_support i).mp hs)

#print axioms row267_support
#print axioms row267_source_zero
theorem row269_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 269 ↔
      i.val ∈ ([71, 72, 73] : List Nat) := by
  revert i
  decide

theorem row269_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([71, 72, 73] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 269 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row269_support i).mp hs)

#print axioms row269_support
#print axioms row269_source_zero
end AspisV8R19.R800SelectedSupportChunk17
