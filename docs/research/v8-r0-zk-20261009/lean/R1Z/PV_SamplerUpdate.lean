import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace R1Z.PV_SamplerUpdate
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
theorem preserve (ops : ExternalFuns)
    (sample : Array U8 32#usize → Result aspis_core.field.wide_exact.WideExact)
    (same : sample=ops.op250) : {ops with op250 := sample}=ops := by
  cases same
  rfl
#print axioms preserve
end R1Z.PV_SamplerUpdate
