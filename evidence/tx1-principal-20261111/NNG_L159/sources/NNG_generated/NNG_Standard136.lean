import NNG_StdFromFn
import NNG_StdMapErr
import NNG_Equality136
set_option autoImplicit false
namespace AspisR1.NNG_Standard136
open Aeneas Aeneas.Std Result NNG_Emitted

/-- Interpret only opaque standard primitives. Every child operation,
including mark, remains the supplying CLOSED child's raw call; no VLib
field instance is defined or overridden here. -/
def install (children : Calls) : Calls :=
  {children with
    c0 := NNG_StdArray.implementation
    c1 := NNG_StdMapErr.run
    c2 := NNG_Equality136.pointEq
    c3 := NNG_Equality136.qeq}
end AspisR1.NNG_Standard136
