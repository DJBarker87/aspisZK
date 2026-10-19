import AspisR1RhoInit.Types

/-! Universally quantified external reservation type/operation. No semantic
success, vector frame or optimization-equivalence property is assumed here.
-/
set_option autoImplicit false
namespace AspisR1CuRho
open Aeneas Aeneas.Std Result
class HeapReserve where
  ReserveError : Type
  reserve : {T : Type} → (A : Type) → alloc.vec.Vec T → Usize →
    Result ((core.result.Result Unit ReserveError) × alloc.vec.Vec T)
abbrev alloc.collections.TryReserveError [HeapReserve] := HeapReserve.ReserveError
#print axioms HeapReserve
end AspisR1CuRho
