import Hist_Store
set_option autoImplicit false
namespace AspisR1.CPP_TraceAppend
open Hist_Store

theorem append (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    {before middle after : Store} {first rest : List S2X.AccountEvent}
    (head : Trace ops id before first middle) (tail : Trace ops id middle rest after) :
    Trace ops id before (first ++ rest) after := by
  induction head with
  | nil => exact tail
  | cons step trace ih => exact Trace.cons step (ih tail)

#print axioms append
end AspisR1.CPP_TraceAppend
