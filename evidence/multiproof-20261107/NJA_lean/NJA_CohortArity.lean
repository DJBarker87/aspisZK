import NJA_Arity
import R22Stage2LocalBodies

set_option autoImplicit false
namespace NJA_CohortArity
open Aeneas Aeneas.Std Result

def arity : NJA_Multiproof.multiproof.Arity → AspisR1Stage2.multiproof.Arity
  | .Two => .Two
  | .Eight => .Eight

theorem bits (a : NJA_Multiproof.multiproof.Arity) :
    NJA_Multiproof.multiproof.Arity.bits a =
      AspisR1Stage2.multiproof.Arity.bits (arity a) := by
  cases a <;> rfl

theorem levels (a : NJA_Multiproof.multiproof.Arity) :
    NJA_Multiproof.multiproof.Arity.levels a =
      AspisR1Stage2.multiproof.Arity.levels (arity a) := by
  cases a <;> simp [NJA_Multiproof.multiproof.Arity.levels, NJA_Multiproof.multiproof.Arity.bits, NJA_Multiproof.multiproof.LEAF_BITS, AspisR1Stage2.multiproof.Arity.levels, AspisR1Stage2.multiproof.Arity.bits, AspisR1Stage2.multiproof.LEAF_BITS, arity]

theorem index (a : Array U32 16#usize) (i : Usize) :
    NJA_Multiproof.multiproof.index_at a i =
      AspisR1Stage2.multiproof.index_at a i := rfl

-- Eight-way-only helper: exact source equation is retained without claiming a
-- reached binary consumer or promoting either inventory occurrence.
theorem value (a : Array (Array U8 32#usize) 16#usize) (i : Usize) :
    NJA_Multiproof.multiproof.value_at a i =
      AspisR1Stage2.multiproof.value_at a i := rfl

theorem width (a : NJA_Multiproof.multiproof.Arity) :
    NJA_Multiproof.multiproof.Arity.width a =
      AspisR1Stage2.multiproof.Arity.width (arity a) := by
  cases a <;>
    simp only [NJA_Multiproof.multiproof.Arity.width,
      NJA_Multiproof.multiproof.Arity.bits, arity,
      AspisR1Stage2.multiproof.Arity.width,
      AspisR1Stage2.multiproof.Arity.bits, bind_tc_ok]
  all_goals
    simp only [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar,
      UScalar.shiftLeft, Usize.wrapping_shl, UScalar.wrapping_shl]
    have bits := System.Platform.le_numBits
    simp [show 1 < System.Platform.numBits by omega,
      show 3 < System.Platform.numBits by omega,
      Nat.mod_eq_of_lt (show 1 < System.Platform.numBits by omega),
      Nat.mod_eq_of_lt (show 3 < System.Platform.numBits by omega)]

#print axioms width
#print axioms bits
#print axioms levels
#print axioms index
#print axioms value
end NJA_CohortArity
