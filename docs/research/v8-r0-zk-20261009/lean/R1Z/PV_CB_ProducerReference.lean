import R1Z.PV_CB_ProducerSelected
import R1Z.PV_CB_CompressSelectedCanonical
import R1Z.PV_CB_Op223TagCanonical
import R1Z.PV_CB_CanonicalSampler
import R1Z.PV_CB_Op223Domain
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_ProducerReference
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_ProducerLimb
variable [ExternalTypes]

theorem slice_valid (ops : ExternalFuns) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple)
    (vt : TraceReads trace) (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs)
    (values : Array U32 16#usize)
    (produced : @host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops)
      trace input = ok (.Ok values)) :
    PV_CB_CompressCanonicalRead.Valid (Array.to_slice values) :=
  PV_CB_ProducerSelected.successful_array ops trace input vt vo values produced

/-- The actual16-value producer supplies the array invariant; tag and lambda
    numerical invariants are derived from their extracted/retained producers.
    The native compressor association is neither assumed nor concluded. -/
theorem sampled (ops : ExternalFuns) (trace : Trace) (input : PV_CB_ProducerTuple.Tuple)
    (vt : TraceReads trace) (vo : PV_CB_CanonicalArrays.Valid OffsetValid input.limbs)
    (values : Array U32 16#usize)
    (produced : @host_semantic.copy_tuple_values _ (PV_CurrentScaleInstall.selected ops)
      trace input = ok (.Ok values)) (id : U16) (block : Array U8 32#usize) :
    ∃ result, (do
      let tag ← PV_CB_ShippedOp223Tag.copy_tag id
      let lambda ← ProverRwFullSampler.selected block
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)
        tag (Array.to_slice values) lambda) = ok result ∧ PV_CB_CanonicalTower.Valid result := by
  obtain ⟨lambda,hl,vl⟩ := PV_CB_CanonicalSampler.selected block
  obtain ⟨result,hr,vr⟩ := PV_CB_CompressSelectedCanonical.reference ops
    (PV_CB_Op223TagCanonical.tag id) (Array.to_slice values) lambda
    (PV_CB_Op223TagCanonical.canonical id) (slice_valid ops trace input vt vo values produced) vl
  refine ⟨result,?_,vr⟩
  simp only [PV_CB_Op223TagCanonical.expression,hl,hr,bind_tc_ok]
#print axioms slice_valid
#print axioms sampled
end R1Z.PV_CB_ProducerReference
