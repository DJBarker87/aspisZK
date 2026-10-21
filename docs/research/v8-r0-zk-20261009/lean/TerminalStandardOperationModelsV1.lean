import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import SelectorArrayMapRuntimeSlice

/-!
Namespace-rebound operational models for standard operations used by the
current terminal extraction.  `Result.map_err` is copied from the accepted
`AspisR1ViewParseProbe.CallerStdModels` body; `Array.map` delegates to the
existing state-threaded Aeneas model.  `Result.map` follows the corresponding
Rust/Aeneas match and callback order.  These definitions model the operations;
the Rust library source correspondence remains a separate obligation.
-/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe

def core.result.Result.map
    {T E U F : Type}
    (callback : core.ops.function.FnOnce F T U)
    (self : core.result.Result T E) (op : F) : Result (core.result.Result U E) := do
  match self with
  | .Ok value =>
      let mapped ← callback.call_once op value
      .ok (.Ok mapped)
  | .Err error => .ok (.Err error)

def core.result.Result.map_err
    {T E F O : Type}
    (callback : core.ops.function.FnOnce O E F)
    (self : core.result.Result T E) (op : O) : Result (core.result.Result T F) := do
  match self with
  | .Ok value => .ok (.Ok value)
  | .Err error =>
      let mapped ← callback.call_once op error
      .ok (.Err mapped)

def core.array.Array.map
    {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U)
    (self : Array T N) (f : F) : Result (Array U N) :=
  Aeneas.Std.core.array.Array.map callback self f

#print axioms core.result.Result.map
#print axioms core.result.Result.map_err
#print axioms core.array.Array.map

end AspisR1SelectedMaskProbe
