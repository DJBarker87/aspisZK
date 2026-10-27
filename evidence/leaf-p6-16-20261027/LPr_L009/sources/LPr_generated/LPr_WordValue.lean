import Aeneas
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace AspisR1.LPr_WordValue
open Aeneas Aeneas.Std

/-- Four arbitrary native bytes; no canonical-field or decoder-success premise. -/
theorem bits (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv =
      d.bv ++ c.bv ++ b.bv ++ a.bv := by
  change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv] : BitVec 32) = _
  ext i hi
  have bound : i < 32 := by simpa using hi
  rw [BitVec.fromLEBytes_getElem]
  interval_cases i <;>
    simp only [BitVec.getElem_append, UScalarTy.U8_numBits_eq,
      List.getElem_cons_zero, List.getElem_cons_succ,
      show (8:Nat)*4=32 from rfl, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceLT, ↓reduceIte, Nat.reduceSub]
  all_goals rfl

#print axioms bits
end AspisR1.LPr_WordValue
