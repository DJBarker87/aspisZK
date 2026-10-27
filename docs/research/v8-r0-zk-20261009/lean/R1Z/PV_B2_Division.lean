import R1Z.PV_B2_Sampler
import R1Z.PV_B2_OrdinaryReference
set_option autoImplicit false
noncomputable section
namespace PV_B2_Division
open Aeneas Aeneas.Std Result ControlFlow
namespace N
abbrev body := PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0.body
abbrev run := PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0
end N
namespace O
abbrev body := PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop.body
abbrev run := PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop
end O
/-- Equality of complete Results, including out-of-range accesses and divergence,
for every machine remainder and counter; no canonicality premise. -/
theorem body (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    N.body rank r j = O.body rank r j := by
  simp only [N.body,O.body,
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0.body,
    PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop.body,
    PV_B2_Sampler.aspis_core.field.P,PV_B2_OrdinaryReference.aspis_core.field.P]

theorem loop (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    N.run rank r j = O.run rank r j := by
  unfold N.run O.run PV_B2_Sampler.host_sampler.low_base_p_digits_loop1_loop0
    PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop
  have hb : (fun (a,b,c) => N.body a b c) = (fun (a,b,c) => O.body a b c) := by
    funext ⟨a,b,c⟩
    exact body a b c
  rw [hb]
#print axioms body
#print axioms loop
end PV_B2_Division
