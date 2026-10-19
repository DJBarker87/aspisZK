import QueryScanActualScanBridge
import AspisR1QueryScan.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled

theorem mapState_cons {T U F : Type}
    (call : F → T → Result (U × F)) (x : T) (xs : List T) (state : F) :
    AspisV8R19.TraversalRuntime.mapState call (x :: xs) state =
      (do
        let (y, state1) ← call state x
        let (ys, state2) ← AspisV8R19.TraversalRuntime.mapState call xs state1
        ok (y :: ys, state2)) := by
  simp [AspisV8R19.TraversalRuntime.mapState]

#print axioms mapState_cons
end AspisR1QueryScanUnrolled
