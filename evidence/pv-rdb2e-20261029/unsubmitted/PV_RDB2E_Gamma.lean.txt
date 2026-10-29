import R1Z.PV_RDB2E_Low
namespace R1Z.PV_RDB2E_Iterator
open Aeneas Aeneas.Std Result PV_B2_C_Sampler
set_option autoImplicit false

def gamma (b : Array U8 32#usize) : Result aspis_core.field.wide_exact.WideExact := do
  let (ds,q) ← low b
  let n ← lift (U32.wrapping_add q 1#u32)
  let (wrapped,ds1) ← carry ds n
  let ds2 ← if wrapped then do let (_,ds2) ← carry ds1 1#u32; ok ds2 else ok ds1
  host_sampler.decode8 ds2

theorem gamma_complete (b : Array U8 32#usize) : gamma b=host_sampler.gamma_sample b := by
  simp only [gamma,host_sampler.gamma_sample,low_complete,carry_complete]

theorem second_carry_current (ds : Words) (wrapped : Bool) :
    (if wrapped then do let (_,out) ← carry ds 1#u32; ok out else ok ds)=
      (if wrapped then do let (_,out) ← host_sampler.add_small_base_p ds 1#u32; ok out else ok ds) := by
  simp only [carry_complete]

#print axioms gamma_complete
#print axioms second_carry_current
end R1Z.PV_RDB2E_Iterator
