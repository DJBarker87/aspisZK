import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk49
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row988_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 988 ↔
      i.val ∈ ([195, 196, 197, 198] : List Nat) := by
  revert i
  decide

theorem row988_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([195, 196, 197, 198] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 988 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row988_support i).mp hs)

#print axioms row988_support
#print axioms row988_source_zero
theorem row990_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 990 ↔
      i.val ∈ ([197, 198] : List Nat) := by
  revert i
  decide

theorem row990_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([197, 198] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 990 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row990_support i).mp hs)

#print axioms row990_support
#print axioms row990_source_zero
theorem row992_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 992 ↔
      i.val ∈ ([197, 198, 199, 200, 201, 202, 205, 206] : List Nat) := by
  revert i
  decide

theorem row992_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([197, 198, 199, 200, 201, 202, 205, 206] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 992 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row992_support i).mp hs)

#print axioms row992_support
#print axioms row992_source_zero
theorem row994_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 994 ↔
      i.val ∈ ([199, 200] : List Nat) := by
  revert i
  decide

theorem row994_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([199, 200] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 994 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row994_support i).mp hs)

#print axioms row994_support
#print axioms row994_source_zero
end AspisV8R19.R800SelectedSupportChunk49
