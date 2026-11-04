import NFY_Part043
import NFY_OwnerTransport
import AspisR1AdapterReconstruct.Funs
set_option autoImplicit false
namespace NFY_RequestTransport
open Aeneas Aeneas.Std

/-- Request extraction and canonical standard helper preserve the same complete
Result and callback state on every input, with no successful-input restriction. -/
theorem map_err_transport {T E F O : Type}
    (f : core.ops.function.FnOnce O E F) (r : core.result.Result T E) (o : O) :
    AspisR20Request.core.result.Result.map_err f r o =
      AspisR1.Port4C_GeometryStd.mapError f r o := by rfl

/-- Adapter reconstruction uses the identical complete callback/Result law. -/
theorem adapter_map_err_transport {T E F O : Type}
    (f : core.ops.function.FnOnce O E F) (r : core.result.Result T E) (o : O) :
    AspisR1AdapterReconstruct.core.result.Result.map_err f r o =
      AspisR1.Port4C_GeometryStd.mapError f r o := by rfl

#print axioms adapter_map_err_transport
#print axioms map_err_transport
end NFY_RequestTransport
