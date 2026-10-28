import R1Z.ProverRwSamplerArithmetic

/-! Actual selected sampler to retained checked source. This is a local
component equality, including failures/divergence, not a real-experiment join. -/
set_option autoImplicit false
namespace R1Z.ProverRwSamplerTransport
open Aeneas Aeneas.Std Result ControlFlow WP
open ProverRwSamplerArithmetic
namespace New
abbrev divBody := ProverRwSampler.sampler.qm31_div_pass_loop.body
abbrev divLoop := ProverRwSampler.sampler.qm31_div_pass_loop
abbrev divPass := ProverRwSampler.sampler.qm31_div_pass
abbrev byteBody := ProverRwSampler.sampler.qm31_digits_loop0.body
abbrev byteLoop := ProverRwSampler.sampler.qm31_digits_loop0
abbrev digitBody := ProverRwSampler.sampler.qm31_digits_loop1.body
abbrev digitLoop := ProverRwSampler.sampler.qm31_digits_loop1
abbrev digits := ProverRwSampler.sampler.qm31_digits
end New
namespace Old
abbrev divBody := AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body
abbrev divLoop := AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop
abbrev divPass := AspisR1Qm31SamplerIndex.sampler.qm31_div_pass
abbrev byteBody := AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0.body
abbrev byteLoop := AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0
abbrev digitBody := AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1.body
abbrev digitLoop := AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1
abbrev digits := AspisR1Qm31SamplerIndex.sampler.qm31_digits
end Old

theorem div_body (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    New.divBody rank r j = Old.divBody rank r j := by
  unfold New.divBody Old.divBody ProverRwSampler.sampler.qm31_div_pass_loop.body
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body
  by_cases h : j > 0#usize
  · have hj : (1#usize).val ≤ j.val := by change 0 < j.val at h; scalar_tac
    simp only [if_pos h, sub_exact j 1#usize hj, shift_exact,
      ProverRwSampler.aspis_core.field.P, AspisR1Qm31SamplerIndex.field.P, lift]
  · simp only [if_neg h]

theorem div_loop (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    New.divLoop rank r j = Old.divLoop rank r j := by
  unfold New.divLoop Old.divLoop ProverRwSampler.sampler.qm31_div_pass_loop
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop
  have hb : (fun (a,b,c) => New.divBody a b c) =
      (fun (a,b,c) => Old.divBody a b c) := by
    funext ⟨a,b,c⟩
    exact div_body a b c
  rw [hb]

theorem div_pass (rank : Array U32 8#usize) : New.divPass rank = Old.divPass rank := by
  unfold New.divPass Old.divPass ProverRwSampler.sampler.qm31_div_pass
    AspisR1Qm31SamplerIndex.sampler.qm31_div_pass
  simp only [div_loop]

theorem byte_body (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    New.byteBody block rank i = Old.byteBody block rank i := by
  unfold New.byteBody Old.byteBody ProverRwSampler.sampler.qm31_digits_loop0.body
    AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0.body
  by_cases h : i < 8#usize
  · have hi : i.val < 8 := h
    obtain ⟨start,hm,hv⟩ := spec_imp_exists
      (Usize.mul_spec (x := 4#usize) (y := i) (by scalar_tac))
    have hs : start.val = 4*i.val := by simpa using hv
    have he : Usize.wrapping_mul 4#usize i = start :=
      Result.ok.inj ((mul_exact 4#usize i (by scalar_tac)).symm.trans hm)
    simp only [if_pos h, lift, he, hm, bind_tc_ok,
      add_exact start 1#usize (by scalar_tac),
      add_exact start 2#usize (by scalar_tac),
      add_exact start 3#usize (by scalar_tac),
      add_exact i 1#usize (by scalar_tac)]
  · simp only [if_neg h]

theorem byte_loop (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    New.byteLoop block rank i = Old.byteLoop block rank i := by
  unfold New.byteLoop Old.byteLoop ProverRwSampler.sampler.qm31_digits_loop0
    AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0
  have hb : (fun (a,b) => New.byteBody block a b) =
      (fun (a,b) => Old.byteBody block a b) := by
    funext ⟨a,b⟩
    exact byte_body block a b
  rw [hb]

theorem digit_body (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
    New.digitBody rank digits i = Old.digitBody rank digits i := by
  unfold New.digitBody Old.digitBody ProverRwSampler.sampler.qm31_digits_loop1.body
    AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1.body
  by_cases h : i < 4#usize
  · have hi : i.val < 4 := h
    simp only [if_pos h, div_pass, add_exact i 1#usize (by scalar_tac), lift]
  · simp only [if_neg h]

theorem digit_loop (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
    New.digitLoop rank digits i = Old.digitLoop rank digits i := by
  unfold New.digitLoop Old.digitLoop ProverRwSampler.sampler.qm31_digits_loop1
    AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1
  have hb : (fun (a,b,c) => New.digitBody a b c) =
      (fun (a,b,c) => Old.digitBody a b c) := by
    funext ⟨a,b,c⟩
    exact digit_body a b c
  rw [hb]

theorem digits_exact (block : Array U8 32#usize) : New.digits block = Old.digits block := by
  unfold New.digits Old.digits ProverRwSampler.sampler.qm31_digits
    AspisR1Qm31SamplerIndex.sampler.qm31_digits
  simp only [byte_loop, digit_loop]

#print axioms div_body
#print axioms div_loop
#print axioms div_pass
#print axioms byte_body
#print axioms byte_loop
#print axioms digit_body
#print axioms digit_loop
#print axioms digits_exact
end R1Z.ProverRwSamplerTransport
