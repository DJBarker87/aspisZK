import AspisV8R19.R800SelectedSupportPrototype
import AspisV8R19.R798LiteralObservationView
import AspisV8R19.R787PairSupportZero

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace AspisV8R19.R800SelectedSupportChunk43
open AspisV8R17
open AspisV8R19.R798LiteralObservationView
open AspisV8R19.R787PairSupportZero
open AspisV8R19.R738JointObservationModel

local instance (d : Fin 255) (s : Fin 3) (r : Nat) : Decidable (pairSupport d s r) := by
  unfold pairSupport
  infer_instance

variable {F : Type*} [CommRing F]
theorem row934_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 934 ↔
      i.val ∈ ([172, 173] : List Nat) := by
  revert i
  decide

theorem row934_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([172, 173] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 934 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row934_support i).mp hs)

#print axioms row934_support
#print axioms row934_source_zero
theorem row936_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 936 ↔
      i.val ∈ ([172, 173, 174, 175, 176, 177] : List Nat) := by
  revert i
  decide

theorem row936_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([172, 173, 174, 175, 176, 177] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 936 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row936_support i).mp hs)

#print axioms row936_support
#print axioms row936_source_zero
theorem row938_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 938 ↔
      i.val ∈ ([174, 175] : List Nat) := by
  revert i
  decide

theorem row938_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([174, 175] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 938 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row938_support i).mp hs)

#print axioms row938_support
#print axioms row938_source_zero
theorem row940_support (i : Fin 222) :
    pairSupport (columnView i).1 (columnView i).2 940 ↔
      i.val ∈ ([174, 175, 176, 177] : List Nat) := by
  revert i
  decide

theorem row940_source_zero (half alpha a b c : F) (i : Fin 222)
    (h : i.val ∉ ([174, 175, 176, 177] : List Nat)) :
    sourceChord half (direction alpha (columnView i).1 (columnView i).2) a b c 940 = 0 := by
  apply direction_sourceChord_zero_of_not_pairSupport half alpha a b c _ _ _ (by decide)
  exact fun hs => h ((row940_support i).mp hs)

#print axioms row940_support
#print axioms row940_source_zero
end AspisV8R19.R800SelectedSupportChunk43
