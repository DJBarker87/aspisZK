import LPk_Step
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace LPk_Cohort
open AspisR1.SamplerMachineBounds AspisR1.ExtractedQM31SamplerPass
open AspisR1.SourceSamplerByteRank AspisR1GammaCaller.DigitsModel
open AspisR1.SamplerNatModel

theorem body_eq (a : Array U32 8#usize) (r : U64) (j : Usize) :
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body a r j =
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body a r j := by
  simp only [AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body,
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body,
    AspisR1Post25Sampler.field.P, AspisR1Qm31SamplerIndex.field.P]

/-- Exact cohort Result, including the quotient writeback, paired to the
native relation on all bounded remainders and all u32 limbs at valid indices. -/
theorem step_result (a : Array U32 8#usize) (r : U64) (j : Usize)
    (hr : r.val < P) (hj0 : 0 < j.val) (hj8 : j.val ≤ 8) :
    ∃ (j1 : Usize) (q : U32) (r1 : U64),
      AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body a r j =
        ok (cont (a.set j1 q, r1, j1)) ∧ j1.val = j.val - 1 ∧
      LPk_Step.Relation r.val
        (a.val[j.val - 1]'(by have := a.property; change a.val.length = 8 at this; omega)).val
        q.val r1.val := by
  obtain ⟨j1,q,r1,he,hj,hq,hm,hb⟩ := body_success a r j hr hj0 hj8
  refine ⟨j1,q,r1, (body_eq a r j).trans he, hj, ?_⟩
  refine ⟨?_, hb⟩
  rw [hq,hm]
  have h := Nat.mod_add_div (r.val * B + (a.val[j.val-1]'(by
    have := a.property; change a.val.length = 8 at this; omega)).val) P
  rw [Nat.mul_comm P] at h
  omega

/-- All 32-byte blocks succeed in the cohort and have eight base-P digits,
a canonical digit range, and the final quotient at most 256. This reuses the
cohort's checked eight-limb and eight-digit inductions. -/
theorem all_blocks (block : Array U8 32#usize) :
    ∃ (ds : Array U32 8#usize) (q : U32),
      AspisR1Post25Sampler.sampler.low_base_p_digits block = ok (ds,q) ∧
      values ds = ordinaryDigits (rank block) ∧
      q.val = rank block / P^8 ∧ q.val ≤ 256 ∧
      ∀ d ∈ values ds, d < P := by
  obtain ⟨_,ds,q,he,_,_,_⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5.low_base_p_digits_success block
  have h := low_candidate_refines block ds q he
  refine ⟨ds,q,he,h.1,h.2,?_,?_⟩
  · rw [h.2]; exact rank_div_P8_le_256 (rank_lt block)
  · rw [h.1]; exact lowDigits_canonical P_pos 8 (rank block)
#print axioms body_eq
#print axioms step_result
#print axioms all_blocks
end LPk_Cohort
