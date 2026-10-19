import AspisR1RhoHeap.Types
import AspisR1RhoInit.FunsExternal

set_option autoImplicit false
namespace AspisR1CuRho
open Aeneas Aeneas.Std Result
abbrev alloc.vec.Vec.try_reserve_exact [HeapReserve] := @HeapReserve.reserve _
#print axioms alloc.vec.Vec.try_reserve_exact
end AspisR1CuRho
