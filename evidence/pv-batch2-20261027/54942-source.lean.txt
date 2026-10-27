import R1Z.PV_B2_CheckedBytes
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_B2_CheckedDigits
open Aeneas Aeneas.Std Result ControlFlow ProverRwSamplerArithmetic
abbrev N := _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1.body
abbrev O := AspisR1Post25Sampler.sampler.low_base_p_digits_loop1.body

theorem body (rank digits : Array U32 8#usize) (i : Usize) :
    N rank digits i = O rank digits i := by
  unfold N O _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1.body
    AspisR1Post25Sampler.sampler.low_base_p_digits_loop1.body
  by_cases h : i < 8#usize
  · have hi : i.val < 8 := h
    simp only [if_pos h,PV_B2_CheckedDiv.pass,add_exact i 1#usize (by scalar_tac),lift]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨q,d⟩ _
    rfl
  · simp only [if_neg h]

theorem loop (rank digits : Array U32 8#usize) (i : Usize) :
    _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1 rank digits i =
      AspisR1Post25Sampler.sampler.low_base_p_digits_loop1 rank digits i := by
  unfold _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1
    AspisR1Post25Sampler.sampler.low_base_p_digits_loop1
  have hb : (fun (a,b,c) => N a b c) = (fun (a,b,c) => O a b c) := by
    funext ⟨a,b,c⟩
    exact body a b c
  rw [hb]

theorem digits (block : Array U8 32#usize) :
    _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits block =
      AspisR1Post25Sampler.sampler.low_base_p_digits block := by
  unfold _root_.PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits
    AspisR1Post25Sampler.sampler.low_base_p_digits
  simp only [PV_B2_CheckedBytes.loop,loop]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro rank _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨q,d⟩ _
  rfl
#print axioms body
#print axioms loop
#print axioms digits
end R1Z.PV_B2_CheckedDigits
