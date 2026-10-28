import R1Z.PV_B2_OrdinaryReference
import R1Z.ProverRwSamplerArithmetic
import AspisR1Post25Sampler.Funs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_B2_CheckedDiv
open Aeneas Aeneas.Std Result ControlFlow ProverRwSamplerArithmetic
abbrev N := _root_.PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop.body
abbrev O := AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body

theorem body (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    N rank r j = O rank r j := by
  unfold N O _root_.PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop.body
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  by_cases h : j > 0#usize
  · have hj : (1#usize).val ≤ j.val := by change 0 < j.val at h; scalar_tac
    simp only [if_pos h,sub_exact j 1#usize hj,shift_exact,
      _root_.PV_B2_OrdinaryReference.aspis_core.field.P,AspisR1Post25Sampler.field.P,lift]
  · simp only [if_neg h]

theorem loop (rank : Array U32 8#usize) (r : U64) (j : Usize) :
    _root_.PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop rank r j =
      AspisR1Post25Sampler.sampler.qm31_div_pass_loop rank r j := by
  unfold _root_.PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass_loop
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop
  have hb : (fun (a,b,c) => N a b c) = (fun (a,b,c) => O a b c) := by
    funext ⟨a,b,c⟩
    exact body a b c
  rw [hb]

theorem pass (rank : Array U32 8#usize) :
    _root_.PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass rank =
      AspisR1Post25Sampler.sampler.qm31_div_pass rank := by
  unfold _root_.PV_B2_OrdinaryReference.sampler_owned.qm31_div_pass
    AspisR1Post25Sampler.sampler.qm31_div_pass
  simp only [loop]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨a,b⟩ _
  rfl
theorem zero (rank : Array U32 8#usize) (r : U64) :
    N rank r 0#usize = ok (done (rank,r)) := rfl
#print axioms zero
#print axioms body
#print axioms loop
#print axioms pass
end R1Z.PV_B2_CheckedDiv
