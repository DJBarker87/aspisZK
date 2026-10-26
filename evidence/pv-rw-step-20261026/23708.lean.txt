import R1Z.PV_RW_SamplerLimbSource
import R1Z.PV_RW_SamplerLimbBounds
set_option autoImplicit false
namespace R1Z.PV_RW_SamplerLimbTotal
open Aeneas Aeneas.Std Result WP

def divisor : U64 := core.convert.num.FromU64U32.from PV_OrdinarySource.aspis_core.field.P

theorem divisor_value : divisor.val = 2147483647 := by
  unfold divisor PV_OrdinarySource.aspis_core.field.P
  rfl

theorem owned_total (word : U32) (remainder : U64) :
    ∃ quotient next, PV_RW_SamplerLimbSource.owned word remainder = ok (quotient,next) ∧
      next.val < PV_RW_SamplerLimbBounds.p := by
  let dividend : U64 := U64.wrapping_shl remainder 32#u32 |||
    core.convert.num.FromU64U32.from word
  have nonzero : divisor.val ≠ 0 := by rw [divisor_value]; omega
  obtain ⟨quotient,hq,_⟩ := UScalar.div_spec dividend nonzero
  obtain ⟨next,hn,hvalue⟩ := spec_imp_exists (U64.rem_spec dividend nonzero)
  refine ⟨UScalar.cast .U32 quotient,next,?_,?_⟩
  · change (do
      let q ← dividend / divisor
      let r ← dividend % divisor
      ok (UScalar.cast .U32 q,r)) = _
    rw [hq]
    simp only [bind_tc_ok,hn]
  · change next.val = dividend.val % divisor.val at hvalue
    rw [hvalue,divisor_value]
    exact Nat.mod_lt _ PV_RW_SamplerLimbBounds.positive

theorem source_total (word : U32) (remainder : U64) :
    ∃ quotient next,
      PV_RW_SamplerLimbSource.sampler_step.shipped_limb word remainder = ok (quotient,next) ∧
      next.val < PV_RW_SamplerLimbBounds.p := by
  rw [PV_RW_SamplerLimbSource.limb]
  exact owned_total word remainder
#print axioms divisor_value
#print axioms owned_total
#print axioms source_total
end R1Z.PV_RW_SamplerLimbTotal
