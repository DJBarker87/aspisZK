import R1Z.PV_CB_CanonicalArrays
import R1Z.PV_CB_CanonicalComplex
import R1Z.PV_CB_CanonicalConstants
import R1Z.PV_CB_CanonicalFill
import R1Z.PV_CB_CanonicalForward
import R1Z.PV_CB_CanonicalHorner
import R1Z.PV_CB_CanonicalLinears
import R1Z.PV_CB_CanonicalLinearsLoop
import R1Z.PV_CB_CanonicalM31
import R1Z.PV_CB_CanonicalM31Ops
import R1Z.PV_CB_CanonicalMaskBasis
import R1Z.PV_CB_CanonicalMaskCell
import R1Z.PV_CB_CanonicalMaskRoot
import R1Z.PV_CB_CanonicalNeg
import R1Z.PV_CB_CanonicalPower26
import R1Z.PV_CB_CanonicalPreparedCtor
import R1Z.PV_CB_CanonicalPreparedMul
import R1Z.PV_CB_CanonicalPreparedPart
import R1Z.PV_CB_CanonicalQuartic
import R1Z.PV_CB_CanonicalQuarticMore
import R1Z.PV_CB_CanonicalSampler
import R1Z.PV_CB_CanonicalTower
import R1Z.PV_CB_CanonicalUpdate
import R1Z.PV_CB_CurrentComplex
import R1Z.PV_CB_CurrentComplexMore
import R1Z.PV_CB_CurrentNeg
import R1Z.PV_CB_CurrentQuartic
import R1Z.PV_CB_CurrentTotal
import R1Z.PV_CB_FillCellEq
import R1Z.PV_CB_FillLoopsEq
import R1Z.PV_CB_FillStepsEq
import R1Z.PV_CB_FiniteStepEq
import R1Z.PV_CB_ForwardLoop
import R1Z.PV_CB_ForwardRange
import R1Z.PV_CB_MaskCell
import R1Z.PV_CB_MaskExponentTables
import R1Z.PV_CB_MaskFillBody
import R1Z.PV_CB_MaskFillLoop
import R1Z.PV_CB_MaskHorner
import R1Z.PV_CB_MaskIndices
import R1Z.PV_CB_MaskLeaves
import R1Z.PV_CB_MaskLinearsFinite
import R1Z.PV_CB_MaskRootEq
import R1Z.PV_CB_MaskSource
import R1Z.PV_CB_OwnedMask
import R1Z.PV_CB_OwnedMaskFill
import R1Z.PV_CB_OwnedMaskHorner
import R1Z.PV_CB_OwnedMaskHornerEq
import R1Z.PV_CB_OwnedMaskLeaves
import R1Z.PV_CB_OwnedMaskLinears
import R1Z.PV_CB_OwnedMaskLinearsEq
import R1Z.PV_CB_PreparedTotal
import R1Z.PV_CB_QuarticProjections
import R1Z.PV_CB_ReverseWrap
set_option autoImplicit false
#print axioms R1Z.PV_CB_CanonicalArrays.read
#print axioms R1Z.PV_CB_CanonicalArrays.repeat_valid
#print axioms R1Z.PV_CB_CanonicalComplex.add
#print axioms R1Z.PV_CB_CanonicalComplex.mul
#print axioms R1Z.PV_CB_CanonicalComplex.r
#print axioms R1Z.PV_CB_CanonicalComplex.source
#print axioms R1Z.PV_CB_CanonicalComplex.sub
#print axioms R1Z.PV_CB_CanonicalComplex.valid_current
#print axioms R1Z.PV_CB_CanonicalConstants.one
#print axioms R1Z.PV_CB_CanonicalConstants.zero
#print axioms R1Z.PV_CB_CanonicalFill.c1
#print axioms R1Z.PV_CB_CanonicalFill.mask
#print axioms R1Z.PV_CB_CanonicalFill.owned_c1
#print axioms R1Z.PV_CB_CanonicalFill.owned_mask
#print axioms R1Z.PV_CB_CanonicalForward.finite
#print axioms R1Z.PV_CB_CanonicalHorner.finite
#print axioms R1Z.PV_CB_CanonicalHorner.owned
#print axioms R1Z.PV_CB_CanonicalHorner.source
#print axioms R1Z.PV_CB_CanonicalLinears.source
#print axioms R1Z.PV_CB_CanonicalLinearsLoop.finite
#print axioms R1Z.PV_CB_CanonicalLinearsLoop.source
#print axioms R1Z.PV_CB_CanonicalM31.mul
#print axioms R1Z.PV_CB_CanonicalM31.reduce
#print axioms R1Z.PV_CB_CanonicalM31Ops.add
#print axioms R1Z.PV_CB_CanonicalM31Ops.double
#print axioms R1Z.PV_CB_CanonicalM31Ops.sub
#print axioms R1Z.PV_CB_CanonicalMaskBasis.i
#print axioms R1Z.PV_CB_CanonicalMaskBasis.r
#print axioms R1Z.PV_CB_CanonicalMaskBasis.tower
#print axioms R1Z.PV_CB_CanonicalMaskCell.cell
#print axioms R1Z.PV_CB_CanonicalMaskRoot.owned
#print axioms R1Z.PV_CB_CanonicalMaskRoot.source
#print axioms R1Z.PV_CB_CanonicalNeg.neg
#print axioms R1Z.PV_CB_CanonicalPower26.power26
#print axioms R1Z.PV_CB_CanonicalPreparedCtor.new
#print axioms R1Z.PV_CB_CanonicalPreparedCtor.new_part
#print axioms R1Z.PV_CB_CanonicalPreparedMul.mul
#print axioms R1Z.PV_CB_CanonicalPreparedPart.mul_part
#print axioms R1Z.PV_CB_CanonicalQuartic.add
#print axioms R1Z.PV_CB_CanonicalQuartic.mul
#print axioms R1Z.PV_CB_CanonicalQuarticMore.scale
#print axioms R1Z.PV_CB_CanonicalQuarticMore.square
#print axioms R1Z.PV_CB_CanonicalSampler.installed
#print axioms R1Z.PV_CB_CanonicalSampler.selected
#print axioms R1Z.PV_CB_CanonicalTower.old_roundtrip
#print axioms R1Z.PV_CB_CanonicalTower.roundtrip
#print axioms R1Z.PV_CB_CanonicalTower.source
#print axioms R1Z.PV_CB_CanonicalTower.source_current
#print axioms R1Z.PV_CB_CanonicalTower.valid_current
#print axioms R1Z.PV_CB_CanonicalUpdate.list_set
#print axioms R1Z.PV_CB_CanonicalUpdate.update
#print axioms R1Z.PV_CB_CurrentComplex.add
#print axioms R1Z.PV_CB_CurrentComplex.mul
#print axioms R1Z.PV_CB_CurrentComplex.sub
#print axioms R1Z.PV_CB_CurrentComplexMore.double
#print axioms R1Z.PV_CB_CurrentComplexMore.scale
#print axioms R1Z.PV_CB_CurrentComplexMore.square
#print axioms R1Z.PV_CB_CurrentNeg.mask_false
#print axioms R1Z.PV_CB_CurrentNeg.mask_true
#print axioms R1Z.PV_CB_CurrentNeg.native
#print axioms R1Z.PV_CB_CurrentQuartic.add
#print axioms R1Z.PV_CB_CurrentQuartic.mul
#print axioms R1Z.PV_CB_CurrentQuartic.r
#print axioms R1Z.PV_CB_CurrentQuartic.scale
#print axioms R1Z.PV_CB_CurrentQuartic.square
#print axioms R1Z.PV_CB_CurrentTotal.c_add
#print axioms R1Z.PV_CB_CurrentTotal.c_double
#print axioms R1Z.PV_CB_CurrentTotal.c_mul
#print axioms R1Z.PV_CB_CurrentTotal.c_r
#print axioms R1Z.PV_CB_CurrentTotal.c_scale
#print axioms R1Z.PV_CB_CurrentTotal.c_square
#print axioms R1Z.PV_CB_CurrentTotal.c_sub
#print axioms R1Z.PV_CB_CurrentTotal.m_add
#print axioms R1Z.PV_CB_CurrentTotal.m_double
#print axioms R1Z.PV_CB_CurrentTotal.m_mul
#print axioms R1Z.PV_CB_CurrentTotal.m_sub
#print axioms R1Z.PV_CB_CurrentTotal.q_add
#print axioms R1Z.PV_CB_CurrentTotal.q_mul
#print axioms R1Z.PV_CB_CurrentTotal.q_scale
#print axioms R1Z.PV_CB_CurrentTotal.q_square
#print axioms R1Z.PV_CB_FillCellEq.cell
#print axioms R1Z.PV_CB_FillLoopsEq.c1
#print axioms R1Z.PV_CB_FillLoopsEq.mask
#print axioms R1Z.PV_CB_FillStepsEq.c1
#print axioms R1Z.PV_CB_FillStepsEq.mask
#print axioms R1Z.PV_CB_FiniteStepEq.source
#print axioms R1Z.PV_CB_ForwardLoop.source
#print axioms R1Z.PV_CB_ForwardRange.advance_val
#print axioms R1Z.PV_CB_ForwardRange.next_done
#print axioms R1Z.PV_CB_ForwardRange.next_step
#print axioms R1Z.PV_CB_MaskCell.c1_total
#print axioms R1Z.PV_CB_MaskCell.mask_total
#print axioms R1Z.PV_CB_MaskCell.total
#print axioms R1Z.PV_CB_MaskExponentTables.c1
#print axioms R1Z.PV_CB_MaskExponentTables.mask
#print axioms R1Z.PV_CB_MaskExponentTables.read
#print axioms R1Z.PV_CB_MaskFillBody.c1
#print axioms R1Z.PV_CB_MaskFillBody.c1_reply
#print axioms R1Z.PV_CB_MaskFillBody.mask
#print axioms R1Z.PV_CB_MaskFillBody.mask_reply
#print axioms R1Z.PV_CB_MaskFillLoop.c1_finite
#print axioms R1Z.PV_CB_MaskFillLoop.c1_run
#print axioms R1Z.PV_CB_MaskFillLoop.mask_finite
#print axioms R1Z.PV_CB_MaskFillLoop.mask_run
#print axioms R1Z.PV_CB_MaskHorner.source
#print axioms R1Z.PV_CB_MaskIndices.coordinate
#print axioms R1Z.PV_CB_MaskIndices.factors_bound
#print axioms R1Z.PV_CB_MaskIndices.factors_read
#print axioms R1Z.PV_CB_MaskIndices.mask_factors_bound
#print axioms R1Z.PV_CB_MaskIndices.mask_factors_read
#print axioms R1Z.PV_CB_MaskLeaves.i
#print axioms R1Z.PV_CB_MaskLeaves.power
#print axioms R1Z.PV_CB_MaskLeaves.r
#print axioms R1Z.PV_CB_MaskLeaves.tower
#print axioms R1Z.PV_CB_MaskLinearsFinite.source
#print axioms R1Z.PV_CB_MaskRootEq.reference
#print axioms R1Z.PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value
#print axioms R1Z.PV_CB_OwnedMaskFill.c1
#print axioms R1Z.PV_CB_OwnedMaskFill.mask
#print axioms R1Z.PV_CB_OwnedMaskHorner.source
#print axioms R1Z.PV_CB_OwnedMaskHornerEq.source
#print axioms R1Z.PV_CB_OwnedMaskLeaves.mul_i
#print axioms R1Z.PV_CB_OwnedMaskLeaves.mul_r
#print axioms R1Z.PV_CB_OwnedMaskLeaves.tower
#print axioms R1Z.PV_CB_OwnedMaskLeaves.tower_total
#print axioms R1Z.PV_CB_OwnedMaskLinears.source
#print axioms R1Z.PV_CB_OwnedMaskLinearsEq.source
#print axioms R1Z.PV_CB_PreparedTotal.mul
#print axioms R1Z.PV_CB_PreparedTotal.mul_part
#print axioms R1Z.PV_CB_PreparedTotal.new
#print axioms R1Z.PV_CB_PreparedTotal.new_part
#print axioms R1Z.PV_CB_QuarticProjections.result_ext
#print axioms R1Z.PV_CB_QuarticProjections.value_ext
#print axioms R1Z.PV_CB_ReverseWrap.pred_eq
