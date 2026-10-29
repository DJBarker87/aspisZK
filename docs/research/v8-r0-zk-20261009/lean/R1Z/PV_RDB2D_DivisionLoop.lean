import R1Z.PV_RDB2D_DivisionRestoration
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false

def division (q : Words) (r : U64) (j : Usize) : Result (Words × U64) :=
  loop (fun (q,r,j) => divisionBody q r j) (q,r,j)

theorem division_complete (q : Words) (r : U64) (j : Usize) :
    division q r j=host_sampler.low_base_p_digits_loop1_loop0 q r j := by
  unfold division host_sampler.low_base_p_digits_loop1_loop0
  have h : (fun (q,r,j) => divisionBody q r j)=
      (fun (q,r,j) => host_sampler.low_base_p_digits_loop1_loop0.body q r j) := by
    funext ⟨q,r,j⟩
    exact division_body q r j
  rw [h]

theorem reverse_eight (q : Words) :
    division q 0#u64 8#usize=host_sampler.low_base_p_digits_loop1_loop0 q 0#u64 8#usize :=
  division_complete q 0#u64 8#usize

#print axioms division_complete
#print axioms reverse_eight
end R1Z.PV_RDB2D_SamplerRestoration
