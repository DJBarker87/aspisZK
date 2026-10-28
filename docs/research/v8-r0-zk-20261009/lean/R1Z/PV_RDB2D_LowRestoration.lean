import R1Z.PV_RDB2D_DigitsRestoration
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false

def low (block : Array U8 32#usize) : Result (Words × U32) := do
  let q ← host_sampler.low_base_p_digits_loop0 block (Array.repeat 8#usize 0#u32) 0#usize
  let (q1,ds) ← digits q (Array.repeat 8#usize 0#u32) 0#usize
  host_sampler.low_base_p_digits_loop2 1#usize
  let high ← Array.index_usize q1 0#usize
  ok (ds,high)

theorem low_complete (block : Array U8 32#usize) :
    low block=host_sampler.low_base_p_digits block := by
  simp only [low,host_sampler.low_base_p_digits,digits_complete]

/-- Every outer pass supplies the updated quotient to the next reverse pass;
the final high word is read from that same returned quotient array. -/
theorem final_quotient (q ds : Words) (out : Words × Words)
    (h : digits q ds 0#usize=ok out) :
    (do let (q1,_) ← digits q ds 0#usize
        Array.index_usize q1 0#usize)=Array.index_usize out.1 0#usize := by
  simp only [h,bind_tc_ok]

#print axioms low_complete
#print axioms final_quotient
end R1Z.PV_RDB2D_SamplerRestoration
