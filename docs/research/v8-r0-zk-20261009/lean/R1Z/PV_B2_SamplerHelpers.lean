import R1Z.PV_B2_SamplerCarrier
set_option autoImplicit false
noncomputable section
namespace PV_B2_SamplerHelpers
open Aeneas Aeneas.Std Result

theorem bytes_body : PV_B2_249.host_sampler.low_base_p_digits_loop0.body =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop0.body := rfl

theorem bytes_loop : PV_B2_249.host_sampler.low_base_p_digits_loop0 =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop0 := by
  funext b q i
  unfold PV_B2_249.host_sampler.low_base_p_digits_loop0
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop0
  simp only [bytes_body]

theorem division_body : PV_B2_249.host_sampler.low_base_p_digits_loop1_loop0.body =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0.body := by
  funext q r j
  simp only [PV_B2_249.host_sampler.low_base_p_digits_loop1_loop0.body,
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0.body,
    PV_B2_249.aspis_core.field.P,PV_B2_Sampler.aspis_core.field.P]

theorem division_loop : PV_B2_249.host_sampler.low_base_p_digits_loop1_loop0 =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0 := by
  funext q r j
  unfold PV_B2_249.host_sampler.low_base_p_digits_loop1_loop0
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0
  simp only [division_body]

theorem digits_body : PV_B2_249.host_sampler.low_base_p_digits_loop1.body =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1.body := by
  funext q d i
  unfold PV_B2_249.host_sampler.low_base_p_digits_loop1.body
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1.body
  simp only [division_loop]

theorem digits_loop : PV_B2_249.host_sampler.low_base_p_digits_loop1 =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1 := by
  funext q d i
  unfold PV_B2_249.host_sampler.low_base_p_digits_loop1
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1
  simp only [digits_body]

theorem check_loop : PV_B2_249.host_sampler.low_base_p_digits_loop2 =
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop2 := rfl

theorem low : PV_B2_249.host_sampler.low_base_p_digits =
    PV_B2_Sampler.host_sampler.low_base_p_digits := by
  funext b
  unfold PV_B2_249.host_sampler.low_base_p_digits PV_B2_Sampler.host_sampler.low_base_p_digits
  simp only [bytes_loop,digits_loop,check_loop]

theorem carry_body : PV_B2_249.host_sampler.add_small_base_p_loop.body =
    PV_B2_Sampler.host_sampler.add_small_base_p_loop.body := by
  funext d q i
  simp only [PV_B2_249.host_sampler.add_small_base_p_loop.body,
    PV_B2_Sampler.host_sampler.add_small_base_p_loop.body,
    PV_B2_249.aspis_core.field.P,PV_B2_Sampler.aspis_core.field.P]

theorem carry_loop : PV_B2_249.host_sampler.add_small_base_p_loop =
    PV_B2_Sampler.host_sampler.add_small_base_p_loop := by
  funext d q i
  unfold PV_B2_249.host_sampler.add_small_base_p_loop
    PV_B2_Sampler.host_sampler.add_small_base_p_loop
  simp only [carry_body]

theorem small : PV_B2_249.host_sampler.add_small_base_p =
    PV_B2_Sampler.host_sampler.add_small_base_p := by
  funext d q
  unfold PV_B2_249.host_sampler.add_small_base_p PV_B2_Sampler.host_sampler.add_small_base_p
  simp only [carry_loop]
#print axioms bytes_body
#print axioms bytes_loop
#print axioms division_body
#print axioms division_loop
#print axioms digits_body
#print axioms digits_loop
#print axioms check_loop
#print axioms low
#print axioms carry_body
#print axioms carry_loop
#print axioms small
end PV_B2_SamplerHelpers
