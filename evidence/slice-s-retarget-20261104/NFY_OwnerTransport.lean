import RPx_Deployed
import AspisR1TerminalDecoder.Funs
import Port4C_GeometryStd
set_option autoImplicit false
namespace NFY_OwnerTransport
open Aeneas Aeneas.Std

/-- The emitted decoder helper and the canonical installed standard helper
have the same complete Result, including callback failure and divergence.
This justifies fully qualifying the helper in copied proof bodies. -/
theorem map_err_transport {T E F O : Type}
    (f : core.ops.function.FnOnce O E F) (r : core.result.Result T E) (o : O) :
    AspisR1TerminalDecoder.core.result.Result.map_err f r o =
      AspisR1.Port4C_GeometryStd.mapError f r o := by rfl

#print axioms map_err_transport
end NFY_OwnerTransport
