import R1Z.PV_RDB2D_DivisionLoop
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false

def digitsBody (q digits : Words) (d : Usize) :
    Result (ControlFlow (Words × Words × Usize) (Words × Words)) := do
  if d < 8#usize then
    let (q1,remainder) ← division q 0#u64 8#usize
    let digit ← lift (UScalar.cast .U32 remainder)
    let ds1 ← Array.update digits d digit
    let d1 ← lift (Usize.wrapping_add d 1#usize)
    ok (cont (q1,ds1,d1))
  else ok (done (q,digits))

theorem digits_body (q ds : Words) (d : Usize) :
    digitsBody q ds d=host_sampler.low_base_p_digits_loop1.body q ds d := by
  simp only [digitsBody,host_sampler.low_base_p_digits_loop1.body,division_complete]

def digits (q ds : Words) (d : Usize) : Result (Words × Words) :=
  loop (fun (q,ds,d) => digitsBody q ds d) (q,ds,d)

theorem digits_complete (q ds : Words) (d : Usize) :
    digits q ds d=host_sampler.low_base_p_digits_loop1 q ds d := by
  unfold digits host_sampler.low_base_p_digits_loop1
  have h : (fun (q,ds,d) => digitsBody q ds d)=
      (fun (q,ds,d) => host_sampler.low_base_p_digits_loop1.body q ds d) := by
    funext ⟨q,ds,d⟩
    exact digits_body q ds d
  rw [h]

#print axioms digits_body
#print axioms digits_complete
end R1Z.PV_RDB2D_SamplerRestoration
