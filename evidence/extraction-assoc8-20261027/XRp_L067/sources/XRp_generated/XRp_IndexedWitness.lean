import XRp_DivisionWitness
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRp_IndexedWitness
open XRp_DivisionWitness XRp_ReversePass

def quotient : Array U32 8#usize := ⟨[1#u32] ++ List.replicate 7 0#u32,by simp⟩

theorem writes_quotient :
    AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body rank 0#u64 1#usize =
      ok (.cont (quotient,0#u64,0#usize)) := by
  unfold AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
  have hpos : 1#usize > 0#usize := by scalar_tac
  have hsub : 1#usize - 1#usize = ok 0#usize := by scalar_tac
  simp only [if_pos hpos,hsub,bind_tc_ok,AspisR1Post25Sampler.field.P]
  rfl

#print axioms writes_quotient
end XRp_IndexedWitness
