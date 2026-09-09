import SelectedPaymentRecovery

/-! A costed, UNINSTALLED selected-transfer repair control. The old compiler
requires positive outputs; the current selected residuals do not enforce this.
This leaf proves exactly what one proposed inverse-product residual would add.
It does not assume acceptance, decoding success, or a valid payment witness.
No claim is made that the new residual is in the verifier or mask inventory.
-/
set_option autoImplicit false
namespace AspisV8.SelectedTransferPositive
open AspisFormal.ArithmetizationCore AspisV8.SelectedPaymentRecovery

theorem product_inverse_nonzero {K : Type*} [Field K] (r c u : K)
    (h : r*c*u-1=0) : r≠0 ∧ c≠0 := by
  have he := sub_eq_zero.mp h
  constructor
  · intro hr
    rw [hr, zero_mul, zero_mul] at he
    exact zero_ne_one he
  · intro hc
    rw [hc, mul_zero, zero_mul] at he
    exact zero_ne_one he

theorem product_inverse_exists {K : Type*} [Field K] (r c : K)
    (hr : r≠0) (hc : c≠0) : r*c*(r*c)⁻¹-1=0 := by
  rw [mul_inv_cancel₀ (mul_ne_zero hr hc), sub_self]

theorem product_inverse_iff {K : Type*} [Field K] (r c : K) :
    (∃ u, r*c*u-1=0) ↔ r≠0 ∧ c≠0 := by
  constructor
  · rintro ⟨u,hu⟩
    exact product_inverse_nonzero r c u hu
  · rintro ⟨hr,hc⟩
    exact ⟨(r*c)⁻¹,product_inverse_exists r c hr hc⟩

/-- Proposed check at conservation row1014, with z1=recipient, successor.z1
=change, and previously relation-free z3 reserved for the inverse. -/
def ProductInverseResidual (t : Table) : Prop :=
  t 1014 1 * t 1015 1 * t 1014 3 - 1 = 0

theorem selected_source_products_nonzero (t : Table) (h : ValueResiduals t)
    (c : ConservationResiduals t) (positive : ProductInverseResidual t) :
    sourceValue t 1≠0 ∧ sourceValue t 2≠0 := by
  have localNonzero := product_inverse_nonzero (t 1014 1) (t 1015 1) (t 1014 3) positive
  have source₁ := sub_eq_zero.mp (h.sourceCopy 1)
  have source₂ := sub_eq_zero.mp (h.sourceCopy 2)
  norm_num [valueBase] at source₁ source₂
  have first : sourceValue t 1=t 1014 1 :=
    source₁.trans (sub_eq_zero.mp c.recipientCopy)
  have second : sourceValue t 2=t 1015 1 :=
    source₂.trans (sub_eq_zero.mp c.changeCopy)
  exact ⟨fun hz => localNonzero.1 (first.symm.trans hz),
    fun hz => localNonzero.2 (second.symm.trans hz)⟩

theorem representative_positive (x : F) (h : x≠0) : 0<x.val := by
  apply Nat.pos_of_ne_zero
  intro hv
  have hx : (x.val : F)=x := ZMod.natCast_zmod_val x
  rw [hv, Nat.cast_zero] at hx
  exact h hx.symm

/-- The genuine selected range/copy/conservation prerequisites, reused from
V7's range/no-wrap port, plus the proposed single residual imply the compiler's
strict amount requirements. Input positivity is derived from conservation,
not checked with another inverse or inserted as a premise. -/
theorem selected_strict_amounts (t : Table) (h : ValueResiduals t)
    (c : ConservationResiduals t) (positive : ProductInverseResidual t) :
    (∀ which, 0<decodedValue t which ∧ decodedValue t which<2^30) ∧
    decodedValue t 0=decodedValue t 1+decodedValue t 2 ∧
    decodedValue t 1+decodedValue t 2<2^32 := by
  obtain ⟨hr,hc⟩ := selected_source_products_nonzero t h c positive
  have rp : 0<decodedValue t 1 := representative_positive _ hr
  have cp : 0<decodedValue t 2 := representative_positive _ hc
  have balance := decoded_transfer_conservation t h c
  have ip : 0<decodedValue t 0 := by omega
  refine ⟨?_,balance,decoded_output_sum_fits_u32 t h⟩
  intro which
  refine ⟨?_,decoded_amount_bound t h which⟩
  fin_cases which
  · exact ip
  · exact rp
  · exact cp

#print axioms product_inverse_nonzero
#print axioms product_inverse_exists
#print axioms product_inverse_iff
#print axioms selected_source_products_nonzero
#print axioms representative_positive
#print axioms selected_strict_amounts
end AspisV8.SelectedTransferPositive
