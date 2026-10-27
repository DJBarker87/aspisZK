import R1Z.PV_CB_Op223ForestLocalCallsite
import R1Z.PV_CB_ProducerReference
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ForestSampledCallsite
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb PV_CB_Op223CellSupport
variable [ExternalTypes] [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem endpoint (ops : ExternalFuns) (f g : Compressor)
    (row start count : Usize) (tweak_right : Bool) (out : PV_CB_TupleProducerOffset.Tuple)
    (produced : PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out)
    (trace : Trace)
    (reads : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace)
      (PV_CB_TupleProducerCarrier.tuple out).limbs)
    (id : U16) (block : Array U8 32#usize)
    (source16 : ∀ tag (data : Array U32 16#usize) lambda,
      PV_CB_CanonicalM31.Valid tag → PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid data →
      PV_CB_CanonicalTower.Valid lambda →
      f tag (Array.to_slice data) lambda = g tag (Array.to_slice data) lambda)
    (side : Usize) (values : PV_CB_Op223Callsite.Values) (arity : PV_CB_Op223Callsite.Arity) :
    (do let tag ← PV_CB_ShippedOp223Tag.copy_tag id
        let lambda ← ProverRwFullSampler.selected block
        @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := f}
          trace (PV_CB_TupleProducerCarrier.tuple out) tag lambda side values arity) =
    (do let tag ← PV_CB_ShippedOp223Tag.copy_tag id
        let lambda ← ProverRwFullSampler.selected block
        @host_semantic.copy_endpoint_values _ {(PV_CurrentScaleInstall.selected ops) with op223 := g}
          trace (PV_CB_TupleProducerCarrier.tuple out) tag lambda side values arity) := by
  obtain ⟨lambda,hl,vl⟩ := PV_CB_CanonicalSampler.selected block
  simp only [PV_CB_Op223TagCanonical.expression,hl,bind_tc_ok]
  exact PV_CB_Op223ForestLocalCallsite.endpoint ops f g row start count tweak_right out produced
    trace reads (PV_CB_Op223TagCanonical.tag id) lambda (PV_CB_Op223TagCanonical.canonical id)
    vl source16 side values arity
#print axioms endpoint
end R1Z.PV_CB_ForestSampledCallsite
