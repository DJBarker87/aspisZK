import R1Z.PV_RDB2E_Low
namespace R1Z.PV_RDB2E_Iterator
open Aeneas Aeneas.Std Result PV_B2_C_Sampler
set_option autoImplicit false

def ordinary (b : Array U8 32#usize) : Result aspis_core.field.wide_exact.WideExact := do
  let (ds,_) ← low b
  host_sampler.decode8 ds

theorem ordinary_complete (b : Array U8 32#usize) : ordinary b=host_sampler.ordinary_sample b := by
  simp only [ordinary,host_sampler.ordinary_sample,low_complete]

#print axioms ordinary_complete
end R1Z.PV_RDB2E_Iterator
