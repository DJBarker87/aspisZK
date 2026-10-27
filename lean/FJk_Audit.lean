import FJk_ActiveMaskRegistry
import FJk_ActiveMaskValue
import FJk_ActiveValue
import FJk_ArrayList
import FJk_CarrierRead
import FJk_CompositionContext
import FJk_CompositionValue
import FJk_CompositionWideFold
import FJk_CompositionWideOnRun
import FJk_CopyCanonical
import FJk_CopyDescriptor
import FJk_CopyFold
import FJk_CopyFullFold
import FJk_CopyLoopNonvacuity
import FJk_CopyPatternDescriptor
import FJk_CopyPowersValue
import FJk_CopyRawValue
import FJk_CopyRegistry
import FJk_CopyRowTransport
import FJk_CopyStep
import FJk_CopyWeightBits
import FJk_CopyWeightSimple
import FJk_CopyWeightValue
import FJk_FamilyWide
import FJk_HornerSum
import FJk_HornerValue
import FJk_ListMap
import FJk_MaskModel
import FJk_MaskNonzero
import FJk_MaskValueStep
import FJk_MaskValues
import FJk_Native07Value
import FJk_OccupancyMap
import FJk_OpeningSelected
import FJk_OpeningsModel
import FJk_PackedWide
import FJk_PatternCellValue
import FJk_PatternDescriptorReads
import FJk_PatternInnerValue
import FJk_PatternModel
import FJk_PatternOuterValue
import FJk_PatternRegistry
import FJk_PatternRegistryA
import FJk_PatternRegistryB
import FJk_PatternRegistryC
import FJk_PatternRegistryD
import FJk_PatternValues
import FJk_PatternValuesRaw
import FJk_PolynomialHorner
import FJk_PolynomialMap
import FJk_PoseidonFamily
import FJk_PoseidonPackedAt
import FJk_PoseidonWideOnRun
import FJk_ResidualLane
import FJk_ResidualNaturality
import FJk_ResidualPack
import FJk_ResidualWide
import FJk_ScalarLaneMap
import FJk_SelectorModel
import FJk_SemanticWideOnRun
import FJh_InternalPairValue
import FJh_InternalOnRun
import FJh_SlicePackValue
import FJh_ProjectedCallValue
import FJh_ProjectedArrayValue
import FJh_PreparedCells
import FJh_Native07RawValue
import FJh_WidePack
import FJh_Native07RawWide
import FJh_PoseidonOnComposition
import ARX_Root
import ARX_Nonvacuity
import FIr_Top
import FIr_Nonvacuity
#print axioms AspisR1.FJk_ActiveMaskRegistry.list
#print axioms AspisR1.FJk_ActiveMaskRegistry.value
#print axioms AspisR1.FJk_ActiveMaskValue.value
#print axioms AspisR1.FJk_ActiveValue.loop
#print axioms AspisR1.FJk_ArrayList.value
#print axioms AspisR1.FJk_CarrierRead.value
#print axioms AspisR1.FJk_CompositionContext.value
#print axioms AspisR1.FJk_CompositionValue.value
#print axioms AspisR1.FJk_CompositionWideFold.low
#print axioms AspisR1.FJk_CompositionWideFold.value
#print axioms AspisR1.FJk_CompositionWideOnRun.value
#print axioms AspisR1.FJk_CopyCanonical.value
#print axioms AspisR1.FJk_CopyDescriptor.endpoint_exact
#print axioms AspisR1.FJk_CopyFold.value
#print axioms AspisR1.FJk_CopyFullFold.value
#print axioms AspisR1.FJk_CopyLoopNonvacuity.value
#print axioms AspisR1.FJk_CopyPowersValue.loop
#print axioms AspisR1.FJk_CopyRawValue.value
#print axioms AspisR1.FJk_CopyRegistry.value
#print axioms AspisR1.FJk_CopyRowTransport.cell
#print axioms AspisR1.FJk_CopyRowTransport.value
#print axioms AspisR1.FJk_CopyStep.value
#print axioms AspisR1.FJk_CopyWeightBits.keep
#print axioms AspisR1.FJk_CopyWeightBits.complement
#print axioms AspisR1.FJk_CopyWeightSimple.discriminants
#print axioms AspisR1.FJk_CopyWeightSimple.zero
#print axioms AspisR1.FJk_CopyWeightSimple.transfer
#print axioms AspisR1.FJk_CopyWeightSimple.withdrawal
#print axioms AspisR1.FJk_CopyWeightValue.value
#print axioms AspisR1.FJk_FamilyWide.scalar
#print axioms AspisR1.FJk_HornerSum.value
#print axioms AspisR1.FJk_HornerValue.value
#print axioms AspisR1.FJk_ListMap.getD
#print axioms AspisR1.FJk_MaskModel.m6144
#print axioms AspisR1.FJk_MaskModel.m6145
#print axioms AspisR1.FJk_MaskModel.m4097
#print axioms AspisR1.FJk_MaskModel.m2048
#print axioms AspisR1.FJk_MaskModel.m2049
#print axioms AspisR1.FJk_MaskModel.m1749
#print axioms AspisR1.FJk_MaskModel.m26214
#print axioms AspisR1.FJk_MaskNonzero.positive
#print axioms AspisR1.FJk_MaskValueStep.zero
#print axioms AspisR1.FJk_MaskValueStep.value
#print axioms AspisR1.FJk_MaskValues.m1024
#print axioms AspisR1.FJk_MaskValues.m1536
#print axioms AspisR1.FJk_MaskValues.m1664
#print axioms AspisR1.FJk_MaskValues.m1728
#print axioms AspisR1.FJk_MaskValues.m1744
#print axioms AspisR1.FJk_MaskValues.m1748
#print axioms AspisR1.FJk_MaskValues.m1749
#print axioms AspisR1.FJk_MaskValues.m2048
#print axioms AspisR1.FJk_MaskValues.m2049
#print axioms AspisR1.FJk_MaskValues.m4096
#print axioms AspisR1.FJk_MaskValues.m4097
#print axioms AspisR1.FJk_MaskValues.m6144
#print axioms AspisR1.FJk_MaskValues.m6145
#print axioms AspisR1.FJk_MaskValues.m16384
#print axioms AspisR1.FJk_MaskValues.m24576
#print axioms AspisR1.FJk_MaskValues.m25600
#print axioms AspisR1.FJk_MaskValues.m26112
#print axioms AspisR1.FJk_MaskValues.m26176
#print axioms AspisR1.FJk_MaskValues.m26208
#print axioms AspisR1.FJk_MaskValues.m26212
#print axioms AspisR1.FJk_MaskValues.m26214
#print axioms AspisR1.FJk_MaskValues.s6144
#print axioms AspisR1.FJk_MaskValues.s6145
#print axioms AspisR1.FJk_MaskValues.s4097
#print axioms AspisR1.FJk_MaskValues.s2048
#print axioms AspisR1.FJk_MaskValues.s2049
#print axioms AspisR1.FJk_MaskValues.s1749
#print axioms AspisR1.FJk_MaskValues.s26214
#print axioms AspisR1.FJk_Native07Value.value
#print axioms AspisR1.FJk_OccupancyMap.lanes
#print axioms AspisR1.FJk_OccupancyMap.value
#print axioms AspisR1.FJk_OpeningSelected.indices
#print axioms AspisR1.FJk_OpeningSelected.z
#print axioms AspisR1.FJk_OpeningSelected.succ
#print axioms AspisR1.FJk_OpeningSelected.xor12
#print axioms AspisR1.FJk_OpeningsModel.value
#print axioms AspisR1.FJk_PackedWide.value
#print axioms AspisR1.FJk_PatternCellValue.value
#print axioms AspisR1.FJk_PatternDescriptorReads.kinds
#print axioms AspisR1.FJk_PatternDescriptorReads.offsets
#print axioms AspisR1.FJk_PatternDescriptorReads.columns
#print axioms AspisR1.FJk_PatternInnerValue.value
#print axioms AspisR1.FJk_PatternModel.value
#print axioms AspisR1.FJk_PatternOuterValue.value
#print axioms AspisR1.FJk_PatternRegistry.value
#print axioms AspisR1.FJk_PatternRegistryA.p00
#print axioms AspisR1.FJk_PatternRegistryA.p01
#print axioms AspisR1.FJk_PatternRegistryA.p02
#print axioms AspisR1.FJk_PatternRegistryA.p03
#print axioms AspisR1.FJk_PatternRegistryB.p04
#print axioms AspisR1.FJk_PatternRegistryB.p05
#print axioms AspisR1.FJk_PatternRegistryB.p06
#print axioms AspisR1.FJk_PatternRegistryB.p07
#print axioms AspisR1.FJk_PatternRegistryC.p08
#print axioms AspisR1.FJk_PatternRegistryC.p09
#print axioms AspisR1.FJk_PatternRegistryC.p10
#print axioms AspisR1.FJk_PatternRegistryD.p11
#print axioms AspisR1.FJk_PatternRegistryD.p12
#print axioms AspisR1.FJk_PatternRegistryD.p13
#print axioms AspisR1.FJk_PatternValues.value
#print axioms AspisR1.FJk_PatternValuesRaw.value
#print axioms AspisR1.FJk_PolynomialHorner.value
#print axioms AspisR1.FJk_PolynomialMap.map
#print axioms AspisR1.FJk_NativePolynomial.value
#print axioms AspisR1.FJk_PoseidonFamily.scalar
#print axioms AspisR1.FJk_PoseidonPackedAt.value
#print axioms AspisR1.FJk_PoseidonWideOnRun.value
#print axioms AspisR1.FJk_ResidualLane.value
#print axioms AspisR1.FJk_ResidualNaturality.value
#print axioms AspisR1.FJk_ResidualPack.value
#print axioms AspisR1.FJk_ResidualWide.scalar
#print axioms AspisR1.FJk_ScalarLaneMap.value
#print axioms AspisR1.FJk_SelectorModel.value
#print axioms AspisR1.FJk_SemanticWideOnRun.value
#print axioms AspisR1.ARX_Root.deployed
#print axioms AspisR1.ARX_Nonvacuity.conditional
#print axioms AspisR1.FIr_Top.deployed
#print axioms AspisR1.FIr_Nonvacuity.composed
