import R1Z.PV_CB_ForestProducedValues
import R1Z.PV_CB_ProducerReference
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ForestProducedReference
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes] [PV_CB_ShippedOp223Tuple.ExternalFuns]

theorem sampled (ops : ExternalFuns) (row start count : Usize) (tweak_right : Bool)
    (out : PV_CB_TupleProducerOffset.Tuple)
    (produced : PV_CB_ShippedOp223Tuple.pool_v1.pair_forest_trace.tuple_cells row start count tweak_right = ok out)
    (trace : Trace)
    (reads : PV_CB_CanonicalArrays.Valid (PV_CB_ProducerLocalLimb.Reads trace)
      (PV_CB_TupleProducerCarrier.tuple out).limbs)
    (values : Array U32 16#usize)
    (run : @host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops)
      trace (PV_CB_TupleProducerCarrier.tuple out) = ok (.Ok values))
    (id : U16) (block : Array U8 32#usize) :
    ∃ result, (do
      let tag ← PV_CB_ShippedOp223Tag.copy_tag id
      let lambda ← ProverRwFullSampler.selected block
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)
        tag (Array.to_slice values) lambda) = ok result ∧ PV_CB_CanonicalTower.Valid result := by
  obtain ⟨lambda,hl,vl⟩ := PV_CB_CanonicalSampler.selected block
  obtain ⟨result,hr,vr⟩ := PV_CB_CompressSelectedCanonical.reference ops
    (PV_CB_Op223TagCanonical.tag id) (Array.to_slice values) lambda
    (PV_CB_Op223TagCanonical.canonical id)
    (PV_CB_ForestProducedValues.canonical ops row start count tweak_right out produced trace reads values run) vl
  refine ⟨result,?_,vr⟩
  simp only [PV_CB_Op223TagCanonical.expression,hl,hr,bind_tc_ok]
#print axioms sampled
end R1Z.PV_CB_ForestProducedReference
