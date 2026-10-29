import R1Z.PV_RDB2F_Digits
namespace R1Z.PV_RDB2F_Iterator
open Aeneas Aeneas.Std Result PV_B2_C_Sampler
set_option autoImplicit false

def low (b : Array U8 32#usize) : Result (Words × U32) := do
  let q ← host_sampler.low_base_p_digits_loop0 b (Array.repeat 8#usize 0#u32) 0#usize
  let (q1,ds) ← digits q (Array.repeat 8#usize 0#u32) 0#usize
  host_sampler.low_base_p_digits_loop2 1#usize
  let high ← Array.index_usize q1 0#usize
  ok (ds,high)

theorem low_complete (b : Array U8 32#usize) : low b=host_sampler.low_base_p_digits b := by
  simp only [low,host_sampler.low_base_p_digits,digits_complete]

theorem final_read_uses_returned_quotient (q ds : Words) (out : Words × Words)
    (h : digits q ds 0#usize=ok out) :
    (do let (current,_) ← digits q ds 0#usize
        Array.index_usize current 0#usize)=Array.index_usize out.1 0#usize := by
  simp only [h,bind_tc_ok]; rfl

#print axioms low_complete
#print axioms final_read_uses_returned_quotient
end R1Z.PV_RDB2F_Iterator
