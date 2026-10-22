import AspisR1Post25Sampler.Funs
import ExtractedQM31SamplerIndexedCandidate
import ExtractedQM31SamplerDivision
import R1SamplerRepeatedPass
import AspisR1Qm31SamplerIndex.Funs

/-! Candidate-only output bridge from the Aeneas-emitted indexed eight-pass
loop to the already-checked repeated-pass model. This is not a production
Rust/source equivalence claim. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1Post25Sampler
open AspisR1.ExtractedQM31SamplerIndexedCandidate
open AspisR1.ExtractedQM31SamplerPassLoop
open AspisR1.ExtractedQM31SamplerDivision
open AspisR1.SamplerRepeatedPass

abbrev Block := Array Std.U8 32#usize
abbrev Words := Array Std.U32 8#usize

def values (digits : Array Std.U32 8#usize) : List Nat :=
  digits.val.map UScalar.val

theorem generated_div_pass_eq_index (rank : Words) :
    AspisR1Post25Sampler.sampler.qm31_div_pass rank =
      AspisR1Qm31SamplerIndex.sampler.qm31_div_pass rank := by
  simp only [AspisR1Post25Sampler.sampler.qm31_div_pass,
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass,
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop,
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop,
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body,
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body,
    AspisR1Post25Sampler.field.P, AspisR1Qm31SamplerIndex.field.P]
  rfl

theorem values_length (digits : Array Std.U32 8#usize) : (values digits).length = 8 := by
  simp only [values, List.length_map]
  exact digits.property

theorem values_set_take (digits : Array Std.U32 8#usize) (i : Usize) (d : U32)
    (hi : i.val < 8) :
    (values (digits.set i d)).take (i.val + 1) =
      (values digits).take i.val ++ [d.val] := by
  have hlen : (values digits).length = 8 := values_length digits
  have hset : values (digits.set i d) = (values digits).set i.val d.val := by
    simp only [values, Aeneas.Std.Array.set_val_eq, List.map_set]
  rw [hset, List.take_succ_eq_append_getElem (by simp only [List.length_set]; omega)]
  rw [List.take_set_of_le (Nat.le_refl i.val), List.getElem_set_self]

theorem low_base_p_digits_loop1_unroll (rank : Words)
    (digits : Array Std.U32 8#usize) (i : Usize) :
    sampler.low_base_p_digits_loop1 rank digits i = (do
      let flow ← sampler.low_base_p_digits_loop1.body rank digits i
      match flow with
      | cont (rank1, digits1, i1) => sampler.low_base_p_digits_loop1 rank1 digits1 i1
      | done out => ok out) := by
  conv_lhs => unfold sampler.low_base_p_digits_loop1; rw [loop]
  cases hb : sampler.low_base_p_digits_loop1.body rank digits i with
  | fail e => simp only [hb, bind_tc_fail]
  | div => simp only [hb, bind_tc_div]
  | ok flow =>
    cases flow with
    | done out => simp only [hb, bind_tc_ok]
    | cont next => simp only [hb, bind_tc_ok]; rfl

/-- The emitted loop retains the exact helper quotient array and stores each
    remainder at the current index. -/
theorem low_base_p_digits_loop1_correct (rank : Words)
    (digits : Array Std.U32 8#usize) (i : Usize) (hi : i.val ≤ 8) :
    ∃ outRank : Words, ∃ outDigits : Array Std.U32 8#usize,
      sampler.low_base_p_digits_loop1 rank digits i = ok (outRank, outDigits) ∧
      values outDigits = (values digits).take i.val ++
        (run (8 - i.val) (words rank).reverse).1 ∧
      (words outRank).reverse = (run (8 - i.val) (words rank).reverse).2 := by
  by_cases hlt : i.val < 8
  · obtain ⟨quotient, digit, hpass, hquotient, hdigit, _⟩ := div_pass_correct rank
    have hgenpass : AspisR1Post25Sampler.sampler.qm31_div_pass rank =
        ok (quotient, digit) := (generated_div_pass_eq_index rank).trans hpass
    have hindex : i.val < digits.length := by
      have hlength : digits.val.length = 8 := digits.property
      change i.val < digits.val.length
      omega
    obtain ⟨updated, hup, heq⟩ := WP.spec_imp_exists (Array.update_spec digits i digit hindex)
    have hu : Array.update digits i digit = ok (digits.set i digit) :=
      hup.trans (congrArg Result.ok heq)
    obtain ⟨next, hn, hnext⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    have hvnext : next.val = i.val + 1 := by simpa using hnext
    have hg : i < 8#usize := hlt
    have hbody : sampler.low_base_p_digits_loop1.body rank digits i =
        ok (cont (quotient, digits.set i digit, next)) := by
      simp only [sampler.low_base_p_digits_loop1.body, if_pos hg, hgenpass, bind_tc_ok]
      change (do
        let updated ← Array.update digits i digit
        let i1 ← i + 1#usize
        ok (cont (quotient, updated, i1))) = _
      simp only [hu, hn, bind_tc_ok]
    obtain ⟨outRank, outDigits, hexec, hvalues, hwords⟩ :=
      low_base_p_digits_loop1_correct quotient (digits.set i digit) next (by omega)
    have hcount : 8 - i.val = (8 - next.val) + 1 := by omega
    have hrun : run (8 - i.val) (words rank).reverse =
        (digit.val :: (run (8 - next.val) (words quotient).reverse).1,
         (run (8 - next.val) (words quotient).reverse).2) := by
      rw [hcount]
      simp only [run]
      rw [← hquotient, ← hdigit]
    refine ⟨outRank, outDigits, ?_, ?_, ?_⟩
    · rw [low_base_p_digits_loop1_unroll, hbody]
      simpa only [bind_tc_ok] using hexec
    · rw [hrun]
      simpa only [hvnext, values_set_take digits i digit hlt,
        List.append_assoc, List.singleton_append] using hvalues
    · simpa only [hrun] using hwords
  · have hi8 : i.val = 8 := by omega
    have hg : ¬ i < 8#usize := by change ¬ i.val < 8; omega
    refine ⟨rank, digits, ?_, ?_, ?_⟩
    · rw [low_base_p_digits_loop1_unroll]
      simp only [sampler.low_base_p_digits_loop1.body, if_neg hg, bind_tc_ok]
    · rw [hi8, Nat.sub_self]
      simp only [run, List.append_nil]
      rw [← values_length digits, List.take_length]
    · rw [hi8, Nat.sub_self]
      rfl
termination_by 8 - i.val
decreasing_by omega

/-- With zero-initialized digits, the emitted eight-pass loop is exactly the
    checked indexed-pass digit and quotient model. -/
theorem low_base_p_digits_loop1_eight_indexed (rank : Words) :
    ∃ outRank : Words, ∃ outDigits : Array Std.U32 8#usize,
      sampler.low_base_p_digits_loop1 rank (Array.repeat 8#usize 0#u32) 0#usize =
          ok (outRank, outDigits) ∧
      values outDigits = (indexedPasses 8 rank).1 ∧
      (words outRank).reverse = (words (indexedPasses 8 rank).2).reverse := by
  obtain ⟨outRank, outDigits, hexec, hvalues, hwords⟩ :=
    low_base_p_digits_loop1_correct rank (Array.repeat 8#usize 0#u32) 0#usize (by decide)
  have hidx := indexedPasses_matches 8 rank
  refine ⟨outRank, outDigits, hexec, ?_, ?_⟩
  · simpa only [show (0#usize).val = 0 from rfl, List.take_zero,
      List.nil_append] using hvalues.trans hidx.1.symm
  · exact hwords.trans hidx.2.symm

#print axioms generated_div_pass_eq_index
#print axioms values_set_take
#print axioms low_base_p_digits_loop1_unroll
#print axioms low_base_p_digits_loop1_correct
#print axioms low_base_p_digits_loop1_eight_indexed

end AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge
