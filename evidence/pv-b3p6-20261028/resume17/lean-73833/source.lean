import PV_B3P_MaskSource542227
namespace PV_B3P_MaskSource542227
set_option autoImplicit false

/-- The specification counts all sixteen bits for every input. It is not a
lookup table for the seven masks. -/
theorem ctpop16_nat542 (bits : BitVec 16) :
    (ctpop16_spec542 bits).toNat = bits.cpopNatRec 16 0 := by
  rw [ctpop16_spec542,BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth_of_le (by decide : 16 ≤ 32)]
  exact BitVec.toNat_cpop bits

theorem ctpop16_bound542 (bits : BitVec 16) :
    (ctpop16_spec542 bits).toNat ≤ 16 := by
  rw [ctpop16_spec542,BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth_of_le (by decide : 16 ≤ 32)]
  exact BitVec.toNat_cpop_le bits

theorem cttz16_widen542 (bits : BitVec 16) :
    (cttz16_spec542 bits).toNat = bits.ctz.toNat := by
  rw [cttz16_spec542,BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth_of_le (by decide : 16 ≤ 32)]

theorem cttz16_lower_zero542 (bits : BitVec 16) (index : Nat)
    (lower : index < (cttz16_spec542 bits).toNat) :
    bits.getLsbD index = false := by
  rw [cttz16_widen542] at lower
  exact BitVec.getLsbD_false_of_lt_ctz lower

theorem cttz16_first_set542 (bits : BitVec 16) (nonzero : bits ≠ 0) :
    bits.getLsbD (cttz16_spec542 bits).toNat = true := by
  rw [cttz16_widen542]
  exact BitVec.getLsbD_true_ctz_of_ne_zero nonzero

theorem cttz16_nonzero_bound542 (bits : BitVec 16) (nonzero : bits ≠ 0) :
    (cttz16_spec542 bits).toNat < 16 := by
  rw [cttz16_widen542]
  have h := (BitVec.ctz_lt_iff_ne_zero (x := bits)).2 nonzero
  exact h

#print axioms ctpop16_nat542
#print axioms ctpop16_bound542
#print axioms cttz16_widen542
#print axioms cttz16_lower_zero542
#print axioms cttz16_first_set542
#print axioms cttz16_nonzero_bound542
end PV_B3P_MaskSource542227
