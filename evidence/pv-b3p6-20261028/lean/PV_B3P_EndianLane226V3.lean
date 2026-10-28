import Aeneas.Std
namespace PV_B3P_EndianLane226V3
open Aeneas Aeneas.Std
set_option autoImplicit false

-- Pointwise bit proof; the recursive byte-list encoder is never unfolded.
theorem lane {w : Nat} (v : BitVec w) (i : Nat) (h : 8*i+8 ≤ w)
    (hi : i < v.toLEBytes.length) :
    v.toLEBytes[i] = (v >>> (8*i)).setWidth 8 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [BitVec.getElem_toLEBytes_eq_getElem v i j hi hj (by omega)]
  rw [BitVec.getElem_setWidth,BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_eq_getElem (by omega)]

#print axioms lane
end PV_B3P_EndianLane226V3
