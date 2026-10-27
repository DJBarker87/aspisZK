import R1Z.PV_B2_Division
set_option autoImplicit false
noncomputable section
namespace PV_B2_Digits
open Aeneas Aeneas.Std Result ControlFlow
abbrev N := PV_B2_Sampler.host_sampler.low_base_p_digits_loop1.body
abbrev O := PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1.body

theorem body (q digits : Array U32 8#usize) (i : Usize) :
    N q digits i = O q digits i := by
  unfold N O PV_B2_Sampler.host_sampler.low_base_p_digits_loop1.body
    PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1.body
    PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass
  have hf : PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0 =
      PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop := by
    funext a r j
    exact PV_B2_Division.loop a r j
  rw [hf]
  simp only [bind_assoc_eq,bind_tc_ok,lift]
  by_cases h : i < 8#usize
  · simp only [if_pos h]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨a,b⟩ _
    rfl
  · simp only [if_neg h]

theorem loop (q digits : Array U32 8#usize) (i : Usize) :
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1 q digits i =
      PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1 q digits i := by
  unfold PV_B2_Sampler.host_sampler.low_base_p_digits_loop1
    PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop1
  have hb : (fun (a,b,c) => N a b c) = (fun (a,b,c) => O a b c) := by
    funext ⟨a,b,c⟩
    exact body a b c
  rw [hb]
#print axioms body
#print axioms loop
end PV_B2_Digits
