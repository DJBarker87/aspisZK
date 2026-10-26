import R1Z.PV_CB3_SamplerWordSource
import R1Z.PV_CB3_WordBits
namespace R1Z.PV_CB3_WordArithmetic
open Aeneas Aeneas.Std Result
open PV_CB3_SamplerWord (base radix)
set_option autoImplicit false

theorem denominator_value : PV_CB3_SamplerWordSource.denominator.val = base := by rfl

/-- Connect the exact extracted shift-or expression to the integer recurrence. -/
theorem dividend_value (word : U32) (prior : U64) (bound : prior.val < base) :
    (PV_CB3_SamplerWordSource.dividend word prior).val =
      PV_CB3_SamplerWord.dividend prior.val word.val := by
  change (((prior.bv <<< 32) ||| word.bv.setWidth 64).toNat) = _
  apply PV_CB3_WordBits.dividend_bits
  have br : base < radix := by unfold base radix; omega
  omega

/-- The full extracted Result, with the actual narrowed quotient value. The
prior bound is the internal long-division invariant, not an output premise. -/
theorem total (word : U32) (prior : U64) (bound : prior.val < base) :
    ∃ (q : U32) (r : U64),
      PV_CB3_ShippedOp249word.reference_split.word_step word prior = ok (q,r) ∧
      q.val = PV_CB3_SamplerWord.dividend prior.val word.val / base ∧
      r.val = PV_CB3_SamplerWord.dividend prior.val word.val % base := by
  obtain ⟨q,r,hr,hqv,hrv⟩ := PV_CB3_SamplerWordSource.word_total_spec word prior
  rw [denominator_value, dividend_value word prior bound] at hqv hrv
  have hw : word.val < radix := word.bv.isLt
  have hqb := PV_CB3_SamplerWord.quotient_word_bound prior.val word.val bound hw
  have hc : (UScalar.cast .U32 q).val = q.val := by
    change (q.bv.setWidth 32).toNat = q.bv.toNat
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by rw [hqv]; exact hqb)
  exact ⟨_,r,hr,hc.trans hqv,hrv⟩

#print axioms denominator_value
#print axioms dividend_value
#print axioms total
end R1Z.PV_CB3_WordArithmetic
