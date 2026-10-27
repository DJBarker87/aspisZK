import LPc_BoundaryProducer
import LPc_CallerBounds
import LPc_ChunkFrame
import LPc_DecodeCanonical
import LPc_DecodeSuccess
import LPc_DecodeValues
import LPc_ExpandRows
import LPc_Iteration
import LPc_TailTransport
import LPc_ViewFrame
import LPa_BoundaryWitness
import LPa_Circle
import LPa_Nonvacuity
open Aeneas Aeneas.Std Result XRk_Release XRk_FieldExternal
set_option autoImplicit false
namespace LPc.Nonvacuity
/-- Only the four zero limb values are normalized here, not a recurrence. -/
theorem zero_canonical : LPa.Add.Canonical qzero := by
  norm_num [LPa.Add.Canonical, qzero, UScalar.ofNatCore_val_eq]
/-- Local full28 boundary witness; this is not joint top non-vacuity. -/
theorem boundary_inhabited :
    ∃ p : Array aspis_core.field.QM31 28#usize,
      (∀ q ∈ p.val, LPa.Add.Canonical q) ∧
      r1_semantic.semantic_boundary p = ok qzero := by
  refine ⟨LPa.Boundary.zeroPolynomial, ?_, LPa.Boundary.zero_accepted⟩
  intro q hq
  have eq : q = qzero := by simpa [LPa.Boundary.zeroPolynomial] using hq
  subst q
  exact zero_canonical
end LPc.Nonvacuity
#print axioms LPc.Boundary.decoded_canonical
#print axioms LPc.Check.caller_iff
#print axioms LPc.Check.caller_reject
#print axioms LPc.Decode.step_canonical
#print axioms LPc.Decode.success_canonical
#print axioms LPc.Decode.values_canonical
#print axioms LPc.Decode.values_get
#print axioms LPc.Echeck.append_tail
#print axioms LPc.Echeck.caller_iff
#print axioms LPc.Echeck.count_with_tail
#print axioms LPc.Echeck.tail_class
#print axioms LPc.Expand.caller_rows
#print axioms LPc.Expand.row_high
#print axioms LPc.Expand.row_low
#print axioms LPc.Nonvacuity.boundary_inhabited
#print axioms LPc.Nonvacuity.zero_canonical
#print axioms LPc.Validate.caller_error_bound
#print axioms LPc.Validate.caller_success
#print axioms LPc.View.readset
#print axioms LPc.fold_simulation
#print axioms LPc.window_append
#print axioms compact.check_values
#print axioms verifier.echeck
#print axioms compact.expand_values
#print axioms verifier.candidate.wide_view
#print axioms r1_semantic.claims
#print axioms r1_wire.ValidatedRecord.decode_k
#print axioms r1_wire.validate_record_fields
#print axioms r1_semantic.semantic_boundary
#print axioms fast_pairing.canonical.Dot.push
#print axioms sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once
