import R1Z.PV_RDB2E_IteratorBodies
import R1Z.PV_RDB2D_DivisionLoop
import R1Z.PV_RDB2D_CarryLoop
namespace R1Z.PV_RDB2E_Iterator
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

def division (q : Words) (r : U64) (j : Usize) : Result (Words × U64) :=
  loop (fun (q,r,j) => divisionBody q r j) (q,r,j)
def carryLoop (q : Words) (n : U32) (i : Usize) : Result (Words × U32) :=
  loop (fun (q,n,i) => carryBody q n i) (q,n,i)
def carry (q : Words) (n : U32) : Result (Bool × Words) := do
  let (q1,n1) ← carryLoop q n 0#usize
  ok (n1 != 0#u32,q1)

theorem division_complete (q : Words) (r : U64) (j : Usize) :
    division q r j=PV_RDB2D_SamplerRestoration.division q r j := by
  unfold division PV_RDB2D_SamplerRestoration.division
  have eq : (fun (q,r,j) => divisionBody q r j)=
      (fun (q,r,j) => PV_RDB2D_SamplerRestoration.divisionBody q r j) := by
    funext ⟨q,r,j⟩; exact division_body q r j
  rw [eq]

theorem carry_loop (q : Words) (n : U32) (i : Usize) :
    carryLoop q n i=PV_RDB2D_SamplerRestoration.carryLoop q n i := by
  unfold carryLoop PV_RDB2D_SamplerRestoration.carryLoop
  have eq : (fun (q,n,i) => carryBody q n i)=
      (fun (q,n,i) => PV_RDB2D_SamplerRestoration.carryBody q n i) := by
    funext ⟨q,n,i⟩; exact carry_body q n i
  rw [eq]

theorem carry_complete (q : Words) (n : U32) :
    carry q n=PV_B2_C_Sampler.host_sampler.add_small_base_p q n := by
  simp only [carry,carry_loop,PV_RDB2D_SamplerRestoration.carry_complete.symm,
    PV_RDB2D_SamplerRestoration.carry]

#print axioms division_complete
#print axioms carry_loop
#print axioms carry_complete
end R1Z.PV_RDB2E_Iterator
