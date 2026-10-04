import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk37
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row882_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 882 ↔
      i.val ∈ ([149] : List Nat) := by
  revert i
  decide

theorem row882_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([149] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 882 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row882_support i).mp hs)

#print axioms row882_support
#print axioms row882_source_zero
theorem row884_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 884 ↔
      i.val ∈ ([149, 150, 151] : List Nat) := by
  revert i
  decide

theorem row884_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([149, 150, 151] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 884 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row884_support i).mp hs)

#print axioms row884_support
#print axioms row884_source_zero
theorem row886_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 886 ↔
      i.val ∈ ([150, 151] : List Nat) := by
  revert i
  decide

theorem row886_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([150, 151] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 886 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row886_support i).mp hs)

#print axioms row886_support
#print axioms row886_source_zero
theorem row888_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 888 ↔
      i.val ∈ ([150, 151, 152, 153, 154, 155] : List Nat) := by
  revert i
  decide

theorem row888_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([150, 151, 152, 153, 154, 155] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 888 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row888_support i).mp hs)

#print axioms row888_support
#print axioms row888_source_zero
end AspisV8R19.R800SelectedSupportChunk37
