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
  cases a <;> rfl

theorem index (a : Array U32 16#usize) (i : Usize) :
    NJA_Multiproof.multiproof.index_at a i =
      AspisR1Stage2.multiproof.index_at a i := rfl

-- Eight-way-only helper: exact source equation is retained without claiming a
-- reached binary consumer or promoting either inventory occurrence.
theorem value (a : Array (Array U8 32#usize) 16#usize) (i : Usize) :
    NJA_Multiproof.multiproof.value_at a i =
      AspisR1Stage2.multiproof.value_at a i := rfl

#print axioms bits
#print axioms levels
#print axioms index
#print axioms value
#check UScalar.shl_spec
#print Aeneas.Std.Usize.wrapping_shl
#print Aeneas.Std.UScalar.shl
end NJA_CohortArity
