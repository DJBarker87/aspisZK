import ExtractedQM31SamplerDivision
import ExtractedQM31SamplerBytes
import R1SamplerRepeatedPass

/-! Actual four-pass loop, reusing the existing repeated-division model. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerDigits
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1Qm31SamplerIndex
open SamplerMachineBounds SamplerWordPass SamplerRepeatedPass
open ExtractedQM31SamplerPassLoop ExtractedQM31SamplerDivision
open ExtractedQM31SamplerBytes

def values (digits : Array U32 4#usize) : List Nat := digits.val.map UScalar.val

theorem values_length (digits : Array U32 4#usize) : (values digits).length = 4 := by
  simp only [values, List.length_map]
  exact digits.property

theorem values_set_take (digits : Array U32 4#usize) (i : Usize) (d : U32)
    (hi : i.val < 4) :
    (values (digits.set i d)).take (i.val + 1) = (values digits).take i.val ++ [d.val] := by
  have hlen : (values digits).length = 4 := values_length digits
  have hset : values (digits.set i d) = (values digits).set i.val d.val := by
    simp only [values, Aeneas.Std.Array.set_val_eq, List.map_set]
  rw [hset, List.take_succ_eq_append_getElem (by simp only [List.length_set]; omega)]
  rw [List.take_set_of_le (Nat.le_refl i.val), List.getElem_set_self]

theorem loop1_unroll (rank : Array U32 8#usize) (digits : Array U32 4#usize)
    (i : Usize) :
    sampler.qm31_digits_loop1 rank digits i = (do
      let flow ← sampler.qm31_digits_loop1.body rank digits i
      match flow with
      | cont (rank1, digits1, i1) => sampler.qm31_digits_loop1 rank1 digits1 i1
      | done out => ok out) := by
  conv_lhs => unfold sampler.qm31_digits_loop1; rw [loop]
  cases hb : sampler.qm31_digits_loop1.body rank digits i with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow =>
    cases flow with
    | done out => simp only [hb, bind_tc_ok]
    | cont next => simp only [hb, bind_tc_ok]; rfl

/-- The already-written prefix is retained; all remaining positions are the
model's successive remainders of the complete carried quotient array. -/
theorem loop1_correct (rank : Array U32 8#usize) (digits : Array U32 4#usize)
    (i : Usize) (hi : i.val ≤ 4) :
    ∃ out : Array U32 4#usize,
      sampler.qm31_digits_loop1 rank digits i = ok out ∧
      values out = (values digits).take i.val ++
        (run (4 - i.val) (words rank).reverse).1 := by
  by_cases hlt : i.val < 4
  · obtain ⟨quotient, digit, hpass, hquotient, hdigit, _⟩ := div_pass_correct rank
    have hindex : i.val < digits.length := by
      have hlength : digits.val.length = 4 := digits.property
      change i.val < digits.val.length
      omega
    obtain ⟨updated, hup, heq⟩ := spec_imp_exists (Array.update_spec digits i digit hindex)
    have hu : Array.update digits i digit = ok (digits.set i digit) :=
      hup.trans (congrArg Result.ok heq)
    obtain ⟨next, hn, hnext⟩ := spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hvnext : next.val = i.val + 1 := by simpa using hnext
    have hg : i < 4#usize := hlt
    have hbody : sampler.qm31_digits_loop1.body rank digits i =
        ok (cont (quotient, digits.set i digit, next)) := by
      simp only [sampler.qm31_digits_loop1.body, if_pos hg, hpass, bind_tc_ok]
      change (do
        let a ← Array.update digits i digit
        let i1 ← i + 1#usize
        ok (cont (quotient, a, i1))) = _
      simp only [hu, hn, bind_tc_ok]
    obtain ⟨out, hexec, hvalues⟩ := loop1_correct quotient (digits.set i digit) next (by omega)
    have hcount : 4 - i.val = (4 - next.val) + 1 := by omega
    have hrun : (run (4 - i.val) (words rank).reverse).1 =
        digit.val :: (run (4 - next.val) (words quotient).reverse).1 := by
      rw [hcount]
      simp only [run]
      rw [← hquotient, ← hdigit]
    refine ⟨out, ?_, ?_⟩
    · rw [loop1_unroll, hbody]
      simpa only [bind_tc_ok] using hexec
    · rw [hrun]
      simpa only [hvnext, values_set_take digits i digit hlt,
        List.append_assoc, List.singleton_append] using hvalues
  · have hi4 : i.val = 4 := by omega
    have hg : ¬ i < 4#usize := by change ¬ i.val < 4; omega
    refine ⟨digits, ?_, ?_⟩
    · rw [loop1_unroll]
      simp only [sampler.qm31_digits_loop1.body, if_neg hg, bind_tc_ok]
    · rw [hi4, Nat.sub_self]
      simp only [run, List.append_nil]
      rw [← values_length digits, List.take_length]
termination_by 4 - i.val
decreasing_by omega

/-- No success or canonicality premise: every source block produces exactly
four model digits from the primitive little-endian source words. -/
theorem digits_total (block : Array U8 32#usize) :
    ∃ out : Array U32 4#usize,
      sampler.qm31_digits block = ok out ∧
      values out = SamplerNatModel.qm31Digits
        (wordValue (words (byteWords block)).reverse) ∧
      (∀ d ∈ out.val, d.val < P) := by
  obtain ⟨out, hloop, hvalues⟩ :=
    loop1_correct (byteWords block) (Array.repeat 4#usize 0#u32) (0#usize) (by decide)
  have hv : values out = (run 4 (words (byteWords block)).reverse).1 := by
    simpa only [show (0#usize).val = 0 from rfl, List.take_zero,
      List.nil_append, Nat.sub_zero] using hvalues
  refine ⟨out, ?_, ?_, ?_⟩
  · simp only [sampler.qm31_digits, assemble_total, bind_tc_ok]
    exact hloop
  · rw [hv, run_digits]
    rfl
  · intro d hd
    have hm : d.val ∈ values out := List.mem_map.mpr ⟨d, hd, rfl⟩
    rw [hv] at hm
    exact run_digits_canonical 4 _ d.val hm

#print axioms values_set_take
#print axioms loop1_unroll
#print axioms loop1_correct
#print axioms digits_total

end AspisR1.ExtractedQM31SamplerDigits
