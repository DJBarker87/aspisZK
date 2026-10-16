import AspisR1Qm31SamplerIndex.Funs
import R1SamplerWordPass

/-! Actual extracted owned-array long-division loop. No caller or oracle claim. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerPass
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1Qm31SamplerIndex
open SamplerMachineBounds

theorem source_P_val : field.P.val = P := by
  rw [field.P]
  rfl

theorem shift_success (r : U64) (hr : r.val < P) :
    ∃ s : U64, r <<< 32#i32 = ok s ∧ s.val = r.val <<< 32 := by
  obtain ⟨s, hs, hv, _⟩ := spec_imp_exists
    (U64.ShiftLeft_IScalar_spec r (32#i32) (by decide) (by decide))
  have hbound : r.val <<< 32 < 18446744073709551616 := by
    rw [Nat.shiftLeft_eq]
    have h := dividend_lt_two63 hr (show 0 < B from B_pos)
    norm_num [B] at h
    omega
  have hsize : U64.size = 18446744073709551616 := by
    norm_num [U64.size, U64.numBits]
  refine ⟨s, hs, ?_⟩
  rw [show (32#i32).toNat = 32 from rfl, hsize,
    Nat.mod_eq_of_lt hbound] at hv
  exact hv

/-- One actual loop iteration writes the quotient to the array and preserves
the complete array through `Array.set`; it also returns the bounded remainder. -/
theorem body_success (rank : Array U32 8#usize) (r : U64) (j : Usize)
    (hr : r.val < P) (hj0 : 0 < j.val) (hj8 : j.val ≤ 8) :
    ∃ (j1 : Usize) (q : U32) (r1 : U64),
      sampler.qm31_div_pass_loop.body rank r j =
        ok (cont (rank.set j1 q, r1, j1)) ∧
      j1.val = j.val - 1 ∧
      q.val = (r.val * B + (rank.val[j.val - 1]'
        (by have := rank.property; simp only [UScalar.ofNatCore_val_eq] at this; omega)).val) / P ∧
      r1.val = (r.val * B + (rank.val[j.val - 1]'
        (by have := rank.property; simp only [UScalar.ofNatCore_val_eq] at this; omega)).val) % P ∧
      r1.val < P := by
  obtain ⟨j1, hj, hvj, _⟩ := spec_imp_exists
    (Usize.sub_spec (x := j) (y := 1#usize) (by change 1 ≤ j.val; omega))
  have hvj : j1.val = j.val - 1 := by simpa using hvj
  have hlength : rank.val.length = 8 := rank.property
  have hj1 : j1.val < rank.length := by change j1.val < rank.val.length; omega
  obtain ⟨d, hd, hvd⟩ := spec_imp_exists (Array.index_usize_spec rank j1 hj1)
  obtain ⟨s, hs, hvs⟩ := shift_success r hr
  let dividend : U64 := s ||| core.convert.num.FromU64U32.from d
  let divisor : U64 := core.convert.num.FromU64U32.from field.P
  have hvdBound : d.val < B := d.bv.isLt
  have hvword : dividend.val = r.val * B + d.val := by
    simp only [dividend, UScalar.val_or, core.convert.num.FromU64U32.from_val_eq, hvs]
    exact SamplerWord.packNat r.val d.val hvdBound
  have hvdivisor : divisor.val = P := by
    simpa only [divisor, core.convert.num.FromU64U32.from_val_eq] using source_P_val
  have hnz : divisor.val ≠ 0 := by rw [hvdivisor]; exact Nat.ne_of_gt P_pos
  obtain ⟨q64, hq, hvq⟩ := UScalar.div_spec dividend hnz
  obtain ⟨r1, hm, hvm⟩ := spec_imp_exists (UScalar.rem_spec dividend hnz)
  let q : U32 := UScalar.cast .U32 q64
  have hqval : q.val = (r.val * B + d.val) / P := by
    rw [show q.val = q64.val % 2^32 from UScalar.cast_val_eq _ _]
    rw [hvq, hvword, hvdivisor]
    exact Nat.mod_eq_of_lt (dividend_quotient_lt_B hr hvdBound)
  have hmval : r1.val = (r.val * B + d.val) % P := by
    simpa only [hvword, hvdivisor] using hvm
  obtain ⟨out, hu, hvo⟩ := spec_imp_exists (Array.update_spec rank j1 q hj1)
  have hg : j > 0#usize := hj0
  refine ⟨j1, q, r1, ?_, hvj, ?_, ?_, ?_⟩
  · dsimp only [dividend, divisor] at hq hm
    dsimp only [q] at hu hvo
    simp only [sampler.qm31_div_pass_loop.body, hg, if_pos, hj, hs, hd,
      lift, bind_tc_ok, hq, hu, hm, hvo, q]
  · simpa only [hvd, hvj] using hqval
  · simpa only [hvd, hvj] using hmval
  · rw [hmval]; exact dividend_remainder_lt_P

#print axioms source_P_val
#print axioms shift_success
#print axioms body_success

end AspisR1.ExtractedQM31SamplerPass
