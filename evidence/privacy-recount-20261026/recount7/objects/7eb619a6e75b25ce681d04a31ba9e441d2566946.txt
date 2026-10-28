import R1Z.PV_B2_ByteBits
import R1Z.PV_B2_OrdinaryReference
set_option autoImplicit false
noncomputable section
namespace PV_B2_Bytes
open Aeneas Aeneas.Std Result ControlFlow
abbrev N := PV_B2_Sampler.host_sampler.low_base_p_digits_loop0.body
abbrev O := PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0.body

theorem body (block : Array U8 32#usize) (q : Array U32 8#usize) (i : Usize) :
    N block q i = O block q i := by
  unfold N O PV_B2_Sampler.host_sampler.low_base_p_digits_loop0.body
    PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0.body
  by_cases h : i < 8#usize
  · simp only [if_pos h,lift,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro a _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro b _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro c _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro d _
    rw [← PV_B2_ByteBits.source]
    rfl
  · simp only [if_neg h]

theorem loop (block : Array U8 32#usize) (q : Array U32 8#usize) (i : Usize) :
    PV_B2_Sampler.host_sampler.low_base_p_digits_loop0 block q i =
      PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0 block q i := by
  unfold PV_B2_Sampler.host_sampler.low_base_p_digits_loop0
    PV_B2_OrdinaryReference.sampler_owned.low_base_p_digits_loop0
  have hb : (fun (a,b) => N block a b) = (fun (a,b) => O block a b) := by
    funext ⟨a,b⟩
    exact body block a b
  rw [hb]
#print axioms body
#print axioms loop
end PV_B2_Bytes
