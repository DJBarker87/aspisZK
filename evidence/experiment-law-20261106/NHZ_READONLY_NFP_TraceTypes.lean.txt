import NFP_DotCaller
import NFP_ReturnCuts
import NFI_TraceResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_TraceTypes
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open Port3_NativeQueryBody
abbrev Inverse := Array U32 5#usize
inductive Event where
 | opening (proof : Slice U8) (i : Usize)
 | dots (q : Slice U8) (g : Array E 29#usize)
 | trace (tag : U16) (i : Usize) (value : E)
 | geometry (receiver : verifier.QueryGeometry) (i : Usize)
 | circle (alpha : E) (values : Dots) (inverse : Inverse)
 | fields (q : Slice U8)
 | line (alpha : E) (values : Dots) (inverse : Inverse)
 | product (a b : U32)
 | double (a : U32)
 | one
 | subtract (a b : U32)
 | accumulate (p : verifier.Prepared) (a : verifier.Accumulator) (node : U32)
   (value : E) (pending : verifier.BatchedWeights)
abbrev M := NFI_TraceResult.M Event
def eval {T : Type} (r : Result T) : M T := NFI_TraceResult.lift r
def mark (e : Event) : M Unit := NFI_TraceResult.mark e

theorem pure_result {T : Type} (x : T) : ((pure x : M T)).result=ok x := rfl
#print axioms pure_result
end AspisR1.NFP_TraceTypes
end
