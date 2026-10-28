import R1Z.PV_RDB2D_CarryRestoration
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false

def carryLoop (ds : Words) (n : U32) (i : Usize) : Result (Words × U32) :=
  loop (fun (ds,n,i) => carryBody ds n i) (ds,n,i)

theorem carry_loop (ds : Words) (n : U32) (i : Usize) :
    carryLoop ds n i=host_sampler.add_small_base_p_loop ds n i := by
  unfold carryLoop host_sampler.add_small_base_p_loop
  have h : (fun (ds,n,i) => carryBody ds n i)=
      (fun (ds,n,i) => host_sampler.add_small_base_p_loop.body ds n i) := by
    funext ⟨ds,n,i⟩
    exact carry_body ds n i
  rw [h]

def carry (ds : Words) (n : U32) : Result (Bool × Words) := do
  let (out,high) ← carryLoop ds n 0#usize
  ok (high != 0#u32,out)

theorem carry_complete (ds : Words) (n : U32) :
    carry ds n=host_sampler.add_small_base_p ds n := by
  simp only [carry,host_sampler.add_small_base_p,carry_loop]

#print axioms carry_loop
#print axioms carry_complete
end R1Z.PV_RDB2D_SamplerRestoration
