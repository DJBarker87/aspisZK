import NMX_R4_CallRun
import NMX_R2_StdSource
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallContext
open NMX_R4_CallRun

def ops (c : Context) : AdapterRw.Ops :=
 NMX_R2_StdOps.install c.env c.allocations.clone c.failure
end NMX_R4_CallContext
end
