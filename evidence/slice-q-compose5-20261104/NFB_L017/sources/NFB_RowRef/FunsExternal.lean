import NFB_RowRef.Types
import Port4C_GeometryStd
set_option autoImplicit false
open Aeneas Aeneas.Std Result

def core.result.Result.map_err {T E F O : Type} (f : core.ops.function.FnOnce O E F) :
 core.result.Result T E → O → Result (core.result.Result T F) :=
 AspisR1.Port4C_GeometryStd.mapError f

def NFB_RowRef.aspis_core.r0.FIBRE_COUNT : Result Usize := ok 262144#usize
#print axioms core.result.Result.map_err
#print axioms NFB_RowRef.aspis_core.r0.FIBRE_COUNT
