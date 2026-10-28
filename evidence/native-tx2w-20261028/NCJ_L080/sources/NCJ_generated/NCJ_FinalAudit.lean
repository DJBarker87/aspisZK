import KMX_CopyMeaning
import NCJ_ArrayWindows
import NCJ_BoxParts
import NCJ_BoxWindows
import NCJ_CallLog
import NCJ_CarrierPorts
import NCJ_CellCanon
import NCJ_Constants
import NCJ_ConstructorArrays
import NCJ_ConstructorCM
import NCJ_ConstructorPoints
import NCJ_ConstructorQM
import NCJ_ConstructorSuccessor
import NCJ_ConstructorSuccessorCell
import NCJ_DotInduction
import NCJ_DoubleAssociation
import NCJ_DoubleBridge
import NCJ_FieldDomains
import NCJ_FieldTotal
import NCJ_ForwardRange
import NCJ_Grouping
import NCJ_GuardExact
import NCJ_GuardRejected
import NCJ_HornerBytes
import NCJ_HornerInduction
import NCJ_InspectSlices
import NCJ_PairLength
import NCJ_Permutation
import NCJ_PolynomialAssociation
import NCJ_PolynomialTotal
import NCJ_QEquality
import NCJ_Reverse
import NCJ_ScalarCellTotal
import NCJ_ScalarFoldStep
import NCJ_ShiftTwo
import NCJ_SliceCells
import NCJ_TensorCellTotal
import NCJ_TensorDomains
import NCJ_TensorFrame
import NCJ_TensorInnerTotal
import NCJ_TensorOffsets
import NCJ_TensorOuterStep
import NCJ_WordIdentity
set_option autoImplicit false
#print axioms NCJ_ArrayWindows.ext
#print axioms NCJ_ArrayWindows.factor_ext
#print axioms NCJ_ArrayWindows.points_ext
#print axioms NCJ_BoxParts.source
#print axioms NCJ_BoxParts.record_eq
#print axioms NCJ_BoxWindows.compose
#print axioms NCJ_CallLog.qm_reply
#print axioms NCJ_CallLog.wide_reply
#print axioms NCJ_CallLog.repeated_qm
#print axioms NCJ_CallLog.quarter_square
#print axioms NCJ_CarrierPorts.to_from
#print axioms NCJ_CarrierPorts.from_to
#print axioms NCJ_CarrierPorts.injective_from
#print axioms NCJ_CarrierPorts.exact_wide
#print axioms NCJ_CarrierPorts.exact_return
#print axioms NCJ_CellCanon.slice_read
#print axioms NCJ_CellCanon.array_read
#print axioms NCJ_CellCanon.list_set
#print axioms NCJ_CellCanon.put
#print axioms NCJ_Constants.zero
#print axioms NCJ_Constants.one
#print axioms NCJ_ConstructorArrays.update
#print axioms NCJ_ConstructorArrays.canonical_put
#print axioms NCJ_ConstructorArrays.canonical_pick
#print axioms NCJ_ConstructorArrays.repeated
#print axioms NCJ_ConstructorCM.add
#print axioms NCJ_ConstructorCM.sub
#print axioms NCJ_ConstructorCM.mul
#print axioms NCJ_ConstructorCM.by_r
#print axioms NCJ_ConstructorPoints.source
#print axioms NCJ_ConstructorPoints.wrapper
#print axioms NCJ_ConstructorQM.add
#print axioms NCJ_ConstructorQM.sub
#print axioms NCJ_ConstructorQM.mul
#print axioms NCJ_ConstructorQM.one
#print axioms NCJ_ConstructorQM.zero
#print axioms NCJ_ConstructorQM.double
#print axioms NCJ_ConstructorSuccessor.source
#print axioms NCJ_ConstructorSuccessorCell.source
#print axioms NCJ_DotInduction.source
#print axioms NCJ_DotInduction.initial
#print axioms NCJ_DoubleAssociation.sharing
#print axioms NCJ_DoubleAssociation.constructor
#print axioms NCJ_DoubleBridge.source
#print axioms NCJ_FieldDomains.final_window
#print axioms NCJ_FieldDomains.polynomial_window
#print axioms NCJ_FieldDomains.partial_index
#print axioms NCJ_FieldDomains.partial_partition
#print axioms NCJ_FieldDomains.low_indices
#print axioms NCJ_FieldDomains.point_indices
#print axioms NCJ_FieldTotal.limbs
#print axioms NCJ_FieldTotal.canonical
#print axioms NCJ_FieldTotal.source
#print axioms NCJ_ForwardRange.done
#print axioms NCJ_ForwardRange.active
#print axioms NCJ_ForwardRange.exact_step
#print axioms NCJ_Grouping.contraction
#print axioms NCJ_Grouping.masks
#print axioms NCJ_GuardExact.index
#print axioms NCJ_GuardExact.source
#print axioms NCJ_GuardRejected.wrong_folds
#print axioms NCJ_GuardRejected.s1
#print axioms NCJ_GuardRejected.d
#print axioms NCJ_HornerBytes.source
#print axioms NCJ_HornerBytes.exact_coefficients
#print axioms NCJ_HornerInduction.step_total
#print axioms NCJ_HornerInduction.total
#print axioms NCJ_PairLength.step
#print axioms NCJ_PairLength.first
#print axioms NCJ_PairLength.second
#print axioms NCJ_PairLength.stop
#print axioms NCJ_PairLength.two_folds
#print axioms NCJ_PairLength.reject
#print axioms NCJ_Permutation.source
#print axioms NCJ_PolynomialAssociation.go
#print axioms NCJ_PolynomialAssociation.polynomial
#print axioms NCJ_PolynomialTotal.index_bound
#print axioms NCJ_PolynomialTotal.source_port
#print axioms NCJ_QEquality.cm
#print axioms NCJ_QEquality.qm
#print axioms NCJ_QEquality.lists
#print axioms NCJ_QEquality.arrays
#print axioms NCJ_Reverse.stop
#print axioms NCJ_Reverse.step
#print axioms NCJ_ScalarCellTotal.source
#print axioms NCJ_ScalarFoldStep.active
#print axioms NCJ_ScalarFoldStep.done
#print axioms NCJ_ShiftTwo.value
#print axioms NCJ_SliceCells.read
#print axioms NCJ_SliceCells.update
#print axioms NCJ_SliceCells.length
#print axioms NCJ_SliceCells.frame
#print axioms NCJ_SliceCells.selected
#print axioms NCJ_TensorCellTotal.source
#print axioms NCJ_TensorDomains.positive
#print axioms NCJ_TensorDomains.write_bounds
#print axioms NCJ_TensorDomains.unread_frame
#print axioms NCJ_TensorDomains.lanes_disjoint
#print axioms NCJ_TensorDomains.writes_disjoint
#print axioms NCJ_TensorDomains.final_width
#print axioms NCJ_TensorDomains.dot_caps
#print axioms NCJ_TensorFrame.frame
#print axioms NCJ_TensorFrame.selected
#print axioms NCJ_TensorFrame.descend_frame
#print axioms NCJ_TensorFrame.descend_selected
#print axioms NCJ_TensorInnerTotal.source
#print axioms NCJ_TensorOffsets.value
#print axioms NCJ_TensorOuterStep.active
#print axioms NCJ_TensorOuterStep.done
#print axioms NCJ_WordIdentity.cm
#print axioms NCJ_WordIdentity.qm
#print axioms NCJ_WordIdentity.wide
#print axioms NCJ_WordIdentity.qm_call
#print axioms NCJ_WordIdentity.wide_call

set_option autoImplicit false
namespace NCJ_CopyFrames
/-- Source windows compose to the exact complete value view, with
explicit address/ownership/length obligations left to the native caller. -/
theorem two_windows {α : Type} (src dst : Nat → α) (a n b m k : Nat) :
    KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst a n) b m k =
      if (a≤ k ∧ k< a+n) ∨ (b≤ k ∧ k< b+m) then src k else dst k := by
  rw [KMX_CopyMeaning.loop_spec,KMX_CopyMeaning.loop_spec]
  by_cases first : a≤ k ∧ k< a+n
  · by_cases second : b≤ k ∧ k< b+m <;> simp [first,second]
  · by_cases second : b≤ k ∧ k< b+m <;> simp [first,second]

/-- Source byte identity of a full copy follows pointwise from the actual
indexed-copy law. No hash, root, address or allocation equality replaces it. -/
theorem entire {α : Type} (src dst : Nat → α) (n : Nat) (i : Nat) (hi : i< n) :
    KMX_CopyMeaning.loop src dst 0 n i=src i := by
  rw [KMX_CopyMeaning.copy_prefix,if_pos hi]

#print axioms two_windows
#print axioms entire
end NCJ_CopyFrames
