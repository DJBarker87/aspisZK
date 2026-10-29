import R1Z.PV_RDB2D_LowRestoration
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result PV_B2_C_Sampler
set_option autoImplicit false

def ordinary (block : Array U8 32#usize) : Result aspis_core.field.wide_exact.WideExact := do
  let (ds,_) ← low block
  host_sampler.decode8 ds

theorem ordinary_complete (block : Array U8 32#usize) :
    ordinary block=host_sampler.ordinary_sample block := by
  simp only [ordinary,host_sampler.ordinary_sample,low_complete]

theorem same_decode (ds : Words) :
    host_sampler.decode8 ds = (do
      let out ← aspis_core.field.wide_exact.WideExact.from_limbs ds
      core.option.Option.unwrap out) := rfl

#print axioms ordinary_complete
#print axioms same_decode
end R1Z.PV_RDB2D_SamplerRestoration
