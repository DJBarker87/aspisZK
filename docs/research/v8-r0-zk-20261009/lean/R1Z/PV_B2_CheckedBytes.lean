import R1Z.PV_B2_CheckedDiv
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_B2_CheckedBytes
open Aeneas Aeneas.Std Result ControlFlow WP ProverRwSamplerArithmetic
abbrev N := _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0.body
abbrev O := AspisR1Post25Sampler.sampler.low_base_p_digits_loop0.body

theorem body (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    N block rank i = O block rank i := by
  unfold N O _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0.body
    AspisR1Post25Sampler.sampler.low_base_p_digits_loop0.body
  by_cases h : i < 8#usize
  · have hi : i.val < 8 := h
    obtain ⟨start,hm,hv⟩ := spec_imp_exists
      (Usize.mul_spec (x := 4#usize) (y := i) (by scalar_tac))
    have hs : start.val = 4*i.val := by simpa using hv
    have he : Usize.wrapping_mul 4#usize i = start :=
      Result.ok.inj ((mul_exact 4#usize i (by scalar_tac)).symm.trans hm)
    simp only [if_pos h,lift,he,hm,bind_tc_ok,
      add_exact start 1#usize (by scalar_tac),
      add_exact start 2#usize (by scalar_tac),
      add_exact start 3#usize (by scalar_tac),
      add_exact i 1#usize (by scalar_tac)]
  · simp only [if_neg h]

theorem loop (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
    _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0 block rank i =
      AspisR1Post25Sampler.sampler.low_base_p_digits_loop0 block rank i := by
  unfold _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0
    AspisR1Post25Sampler.sampler.low_base_p_digits_loop0
  have hb : (fun (a,b) => N block a b) = (fun (a,b) => O block a b) := by
    funext ⟨a,b⟩
    exact body block a b
  rw [hb]
#print axioms body
#print axioms loop
end R1Z.PV_B2_CheckedBytes
