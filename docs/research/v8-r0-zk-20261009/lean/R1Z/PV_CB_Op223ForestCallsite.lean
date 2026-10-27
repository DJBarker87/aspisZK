import R1Z.PV_CB_ForestProducerCarrier
import R1Z.PV_CB_Op223CanonicalCallsite
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op223ForestCallsite
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb PV_CB_Op223CellSupport
variable [ExternalTypes] [PV_CB_ShippedOp223Tuple.ExternalFuns]

/-- The actual emitted tuple producer discharges the offset premise of the
    canonical endpoint transport. Native callback agreement and trace-word
    canonicality remain explicit, so no source row is claimed here. -/
theorem endpoint (ops : ExternalFuns) (f g : Compressor)
    (row start count : Usize) (tweak_right : Bool) (out : PV_CB_TupleProducerOffset.Tuple)
    (produced : PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out)
    (trace : Trace) (vt : PV_CB_ProducerTraceData.Valid trace)
    (tag : U32) (lambda : Q) (vtag : PV_CB_CanonicalM31.Valid tag)
    (vlambda : PV_CB_CanonicalTower.Valid lambda)
    (source16 : ∀ tag (data : Array U32 16#usize) lambda,
      PV_CB_CanonicalM31.Valid tag →
      PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid data →
      PV_CB_CanonicalTower.Valid lambda →
      f tag (Array.to_slice data) lambda = g tag (Array.to_slice data) lambda)
    (side : Usize) (values : PV_CB_Op223Callsite.Values) (arity : PV_CB_Op223Callsite.Arity) :
    @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := f}
      trace (PV_CB_TupleProducerCarrier.tuple out) tag lambda side values arity =
    @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := g}
      trace (PV_CB_TupleProducerCarrier.tuple out) tag lambda side values arity :=
  PV_CB_Op223CanonicalCallsite.endpoint ops f g trace (PV_CB_TupleProducerCarrier.tuple out) vt
    (PV_CB_ForestProducerCarrier.produced row start count tweak_right out produced)
    tag lambda vtag vlambda source16 side values arity
#print axioms endpoint
end R1Z.PV_CB_Op223ForestCallsite
