import FJu_Remaining
import FIr_Remaining2
set_option autoImplicit false
namespace AspisR1.FJu_EndpointIdentity
/-- FIr's residual terminal law and this job's residual are literally the same. -/
theorem residual : @FJu_Remaining.Endpoint = @FIr_Remaining2.Endpoint := rfl
#print axioms residual
end AspisR1.FJu_EndpointIdentity
