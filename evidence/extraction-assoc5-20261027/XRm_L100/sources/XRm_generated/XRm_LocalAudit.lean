import XRm_ActualDot
import XRm_AllocationBoundary
import XRm_CandidateAssociation
import XRm_CheckpointCalls
import XRm_CheckpointFinalize
import XRm_CheckpointLayout
import XRm_CheckpointSize
import XRm_CompactLength
import XRm_CompactShape
import XRm_ComplexValues
import XRm_Conversions
import XRm_DotAssociation
import XRm_DotBounds
import XRm_DotNaturalHistory
import XRm_DotNoWrap
import XRm_DotSites
import XRm_FieldCanonical
import XRm_FieldValues
import XRm_GeometryPoint
import XRm_GeometryValues
import XRm_M31Canonical
import XRm_Nonvacuity
import XRm_PointInterpretation
import XRm_PowersCanonical
import XRm_QueryIndices
import XRm_QueryLineStep
import XRm_Reduce
import XRm_ResultCuts
import XRm_ReverseSites
import XRm_ReverseStep
import XRm_TableBlock
import XRm_TableBounds
import XRm_Tx1Cuts
import XRm_VectorEffects
import XRm_WideProducer
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release
namespace XRm_QueryPoint
abbrev F := XRm_FieldValues.M31Exact
/-- The actual query word selects these SAME table words and field-valued
point in one successful emitted body. No separate point-call success is input. -/
theorem reached (start : Usize) (it next : core.slice.iter.Iter U32) (query : U32)
    (lines flat outLines outFlat : alloc.vec.Vec aspis_core.field.M31)
    (hnext : core.slice.iter.IteratorSliceIter.next it=ok (some query,next))
    (run : verifier.QueryGeometry.for_range_loop0.body start it lines flat=ok (.cont (next,outLines,outFlat))) :
    ∃ (point : aspis_core.r0.domain.Point aspis_core.field.M31) (high : Usize) (a b : U32 × U32),
      (UScalar.cast .Usize query)<262144#usize ∧
      fast_domain.fibre_point (UScalar.cast .Usize query)=ok point ∧
      (UScalar.cast .Usize query) >>> 9#i32=ok high ∧
      Array.index_usize fast_domain.TABLE_A ((UScalar.cast .Usize query) &&& 511#usize)=ok a ∧
      Array.index_usize fast_domain.TABLE_B high=ok b ∧
      (point.x.val:F)=(a.1.val:F)*(b.1.val:F)-(a.2.val:F)*(b.2.val:F) ∧
      (point.y.val:F)=(a.1.val:F)*(b.2.val:F)+(a.2.val:F)*(b.1.val:F) := by
  obtain ⟨point,_,_,_,_,_,bound,hpoint,_,_,_,_,_⟩ :=
    XRm_QueryIndices.reached start it next query lines flat outLines outFlat hnext run
  obtain ⟨high,a,b,hh,ha,hb,hx,hy,_,_⟩ :=
    XRm_PointInterpretation.point (UScalar.cast .Usize query) point hpoint
  exact ⟨point,high,a,b,bound,hpoint,hh,ha,hb,hx,hy⟩
#print axioms reached
end XRm_QueryPoint

#print axioms XRm_ActualDot.associated
#print axioms XRm_AllocationBoundary.filled_ne_error
#print axioms XRm_CandidateAssociation.source
#print axioms XRm_CheckpointCalls.calls
#print axioms XRm_CheckpointCalls.slice
#print axioms XRm_CheckpointFinalize.value
#print axioms XRm_CheckpointSize.finish_length
#print axioms XRm_CheckpointSize.model
#print axioms XRm_CompactLength.reject
#print axioms XRm_CompactShape.accepted
#print axioms XRm_ComplexValues.cmul
#print axioms XRm_ComplexValues.reduce
#print axioms XRm_ComplexValues.sum_value
#print axioms XRm_Conversions.widen
#print axioms XRm_DotAssociation.canonical_iff
#print axioms XRm_DotAssociation.prepared_tail
#print axioms XRm_DotBounds.partial_bound
#print axioms XRm_DotBounds.raw
#print axioms XRm_DotBounds.raw_index
#print axioms XRm_DotBounds.step_value
#print axioms XRm_DotBounds.term_bound
#print axioms XRm_DotBounds.u64_value
#print axioms XRm_DotBounds.wrap
#print axioms XRm_DotNaturalHistory.reached
#print axioms XRm_DotNoWrap.fold
#print axioms XRm_DotNoWrap.operands_length
#print axioms XRm_DotNoWrap.zero
#print axioms XRm_DotSites.tail
#print axioms XRm_DotSites.unwrap_unit
#print axioms XRm_FieldCanonical.cadd
#print axioms XRm_FieldCanonical.cmul
#print axioms XRm_FieldCanonical.csub
#print axioms XRm_FieldCanonical.mul
#print axioms XRm_FieldCanonical.mul_by_r
#print axioms XRm_FieldCanonical.qadd
#print axioms XRm_FieldCanonical.qmul
#print axioms XRm_FieldCanonical.qsub
#print axioms XRm_FieldCanonical.reduce
#print axioms XRm_FieldValues.add
#print axioms XRm_FieldValues.add_val
#print axioms XRm_FieldValues.cast_two31_eq_one
#print axioms XRm_FieldValues.mul
#print axioms XRm_FieldValues.reduce_value
#print axioms XRm_FieldValues.residue_mersenneFold31
#print axioms XRm_FieldValues.residue_rawM31ReduceU64
#print axioms XRm_FieldValues.sub
#print axioms XRm_FieldValues.sub_val
#print axioms XRm_GeometryPoint.line
#print axioms XRm_GeometryPoint.low_index
#print axioms XRm_GeometryPoint.point
#print axioms XRm_GeometryPoint.table_value
#print axioms XRm_GeometryValues.line
#print axioms XRm_GeometryValues.z
#print axioms XRm_M31Canonical.add
#print axioms XRm_M31Canonical.sub
#print axioms XRm_Nonvacuity.canonical_one
#print axioms XRm_Nonvacuity.empty_dot
#print axioms XRm_Nonvacuity.noncanonical_history
#print axioms XRm_Nonvacuity.reverse_prefix
#print axioms XRm_PointInterpretation.array_member
#print axioms XRm_PointInterpretation.point
#print axioms XRm_PointInterpretation.table_canonical
#print axioms XRm_PowersCanonical.array_read
#print axioms XRm_PowersCanonical.powers
#print axioms XRm_PowersCanonical.prepared
#print axioms XRm_PowersCanonical.recurrence
#print axioms XRm_QueryIndices.reached
#print axioms XRm_QueryLineStep.continuation
#print axioms XRm_Reduce.canonical
#print axioms XRm_Reduce.extractedFold31_val
#print axioms XRm_Reduce.extractedReduceOut_val
#print axioms XRm_Reduce.extractedSecondFold_val
#print axioms XRm_Reduce.extracted_P_val
#print axioms XRm_Reduce.extracted_reduce_u64_eq_out
#print axioms XRm_Reduce.m31Modulus_eq_two31_sub_one
#print axioms XRm_Reduce.masked31_val
#print axioms XRm_Reduce.mersenneFold31_lt_two34
#print axioms XRm_Reduce.narrowedSecondFold_val
#print axioms XRm_Reduce.rawM31ReduceU64_canonical
#print axioms XRm_Reduce.secondFold_lt_modulus_add_eight
#print axioms XRm_Reduce.secondFold_lt_u32
#print axioms XRm_Reduce.shift31_val
#print axioms XRm_Reduce.u32_size_eq
#print axioms XRm_Reduce.u64_size_eq
#print axioms XRm_Reduce.wrapping_sub_P_val
#print axioms XRm_ResultCuts.fibre
#print axioms XRm_ResultCuts.map_err_ok
#print axioms XRm_Reverse.cursor
#print axioms XRm_ReverseSites.body_cursor
#print axioms XRm_ReverseSites.caller_prefix
#print axioms XRm_ReverseSites.cursor_zero
#print axioms XRm_ReverseSites.nonvacuity
#print axioms XRm_ReverseSites.reverse_site
#print axioms XRm_TableBlock.append
#print axioms XRm_TableBlock.first
#print axioms XRm_TableBounds.A0
#print axioms XRm_TableBounds.A1
#print axioms XRm_TableBounds.A10
#print axioms XRm_TableBounds.A11
#print axioms XRm_TableBounds.A12
#print axioms XRm_TableBounds.A13
#print axioms XRm_TableBounds.A14
#print axioms XRm_TableBounds.A15
#print axioms XRm_TableBounds.A2
#print axioms XRm_TableBounds.A3
#print axioms XRm_TableBounds.A4
#print axioms XRm_TableBounds.A5
#print axioms XRm_TableBounds.A6
#print axioms XRm_TableBounds.A7
#print axioms XRm_TableBounds.A8
#print axioms XRm_TableBounds.A9
#print axioms XRm_TableBounds.B0
#print axioms XRm_TableBounds.B1
#print axioms XRm_TableBounds.B10
#print axioms XRm_TableBounds.B11
#print axioms XRm_TableBounds.B12
#print axioms XRm_TableBounds.B13
#print axioms XRm_TableBounds.B14
#print axioms XRm_TableBounds.B15
#print axioms XRm_TableBounds.B2
#print axioms XRm_TableBounds.B3
#print axioms XRm_TableBounds.B4
#print axioms XRm_TableBounds.B5
#print axioms XRm_TableBounds.B6
#print axioms XRm_TableBounds.B7
#print axioms XRm_TableBounds.B8
#print axioms XRm_TableBounds.B9
#print axioms XRm_TableBounds.tableA
#print axioms XRm_TableBounds.tableB
#print axioms XRm_Tx1Cuts.cuts
#print axioms XRm_VectorEffects.clone
#print axioms XRm_VectorEffects.extend
#print axioms XRm_VectorEffects.push
#print axioms XRm_WideProducer.mul
#print axioms XRm_WideProducer.mul_u
#print axioms XRm_WideProducer.one
#print axioms XRm_WideProducer.qmul_raw
#print axioms XRm_WideProducer.zero
#check @XRm_ActualDot.associated
#check @XRm_ReverseSites.reverse_site
#check @XRm_QueryPoint.reached
#check @XRm_QueryLineStep.continuation
#check @XRm_CandidateAssociation.source
