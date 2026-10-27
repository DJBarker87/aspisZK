import Aeneas
import R1Z.PV_CB_Op223TupleProducerTypes
set_option autoImplicit false
namespace PV_CB_ShippedOp223Tuple
open Aeneas Aeneas.Std Result
/-- Unconstrained range-selector callback. Source postconditions are quantified
    over every instance, including failure/divergence. No source-output law is
    assumed, and no generated external axiom is installed. -/
class ExternalFuns where
  contains : {Idx U : Type} → core.cmp.PartialOrd Idx Idx →
    core.cmp.PartialOrd Idx U → core.cmp.PartialOrd U Idx →
    core.ops.range.Range Idx → U → Result Bool
abbrev core.ops.range.Range.contains [ops : ExternalFuns] := @ExternalFuns.contains ops
end PV_CB_ShippedOp223Tuple
