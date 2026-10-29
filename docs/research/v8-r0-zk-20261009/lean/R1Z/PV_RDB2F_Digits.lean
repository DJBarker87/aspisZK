import R1Z.PV_RDB2F_IteratorLoops
import R1Z.PV_RDB2D_DigitsRestoration
namespace R1Z.PV_RDB2F_Iterator
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false

def digitsBody (q ds : Words) (i : Usize) :
    Result (ControlFlow (Words × Words × Usize) (Words × Words)) := do
  if i < 8#usize then
    let (q1,r) ← division q 0#u64 8#usize
    let value ← lift (UScalar.cast .U32 r)
    let ds1 ← Array.update ds i value
    let j ← lift (Usize.wrapping_add i 1#usize)
    ok (cont (q1,ds1,j))
  else ok (done (q,ds))

def digits (q ds : Words) (i : Usize) : Result (Words × Words) :=
  loop (fun (q,ds,i) => digitsBody q ds i) (q,ds,i)

theorem digits_body (q ds : Words) (i : Usize) :
    digitsBody q ds i=PV_RDB2D_SamplerRestoration.digitsBody q ds i := by
  simp only [digitsBody,PV_RDB2D_SamplerRestoration.digitsBody,division_complete]

theorem digits_complete (q ds : Words) (i : Usize) :
    digits q ds i=host_sampler.low_base_p_digits_loop1 q ds i := by
  unfold digits
  have eq : (fun (q,ds,i) => digitsBody q ds i)=
      (fun (q,ds,i) => PV_RDB2D_SamplerRestoration.digitsBody q ds i) := by
    funext ⟨q,ds,i⟩; exact digits_body q ds i
  rw [eq]
  exact PV_RDB2D_SamplerRestoration.digits_complete q ds i

#print axioms digits_body
#print axioms digits_complete
end R1Z.PV_RDB2F_Iterator
