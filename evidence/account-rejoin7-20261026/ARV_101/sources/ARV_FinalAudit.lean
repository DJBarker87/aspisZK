import P6C_Issued
import P6C_Whole
import ARU_OriginalLaw
import ARU_CoverageQuantifiers
import ARV_Adaptive
import ARV_AdaptiveAccepted
import ARV_AdaptiveChoice
import ARV_AdaptiveOriginal
import ARV_Constant
import ARV_Counterexample
import ARV_Filter
import ARV_FilterCarrier
import ARV_FilterCharge
import ARV_FilterCheckpoint
import ARV_FilterDomination
import ARV_FilterExact
import ARV_FilterJoin
import ARV_FilterMass
import ARV_FilterNumeric
import ARV_FilterOriginal
import ARV_FilterPerCoin
import ARV_FilterPhysical
import ARV_FilterPreserves
import ARV_FilterRange
import ARV_FilterSupport
import ARV_FilterTop
import ARV_FilterWeighted
import ARV_FirstPartial
import ARV_Freeze
import ARV_Fresh
import ARV_LogChange
import ARV_NativeCostGap
import ARV_NativePartial
import ARV_Nonvacuity
import ARV_ObservedSupport
import ARV_OneTuple
import ARV_PaddingChoice
import ARV_PaddingSupport
import ARV_PaddingWork
import ARV_Poison
import ARV_PoisonNative
import ARV_Root
import ARV_Statement_51
import ARV_Statement_52
import ARV_Statement_53
import ARV_Statement_54
import ARV_Statement_55
import ARV_Statement_56
import ARV_Statement_57
import ARV_Statement_58
import ARV_Statement_59
import ARV_Statement_60
import ARV_Statement_61
import ARV_Statement_62
import ARV_Statement_63
import ARV_Statement_64
import ARV_Statement_65
import ARV_Statement_66
import ARV_Statement_67
import ARV_Statement_68
import ARV_Statement_69
import ARV_Statement_70
import ARV_Statement_71
import ARV_Statement_72
import ARV_Statement_73
import ARV_Statement_74
import ARV_Statement_75
import ARV_Statement_76
import ARV_Statement_77
import ARV_Statement_78
import ARV_Statement_79
import ARV_Statement_80
import ARV_Statement_81
import ARV_Statement_82
import ARV_Statement_83
import ARV_Statement_84
import ARV_Statement_85
import ARV_Statement_86
import ARV_Statement_87
import ARV_Statement_88
import ARV_Statement_89
import ARV_Statement_90
import ARV_Statement_91
import ARV_Statement_92
import ARV_Statement_93
import ARV_Statement_94
import ARV_Statement_95
import ARV_Statement_96
import ARV_Statement_97
import ARV_Statement_98
import ARV_UniversalRefutation
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140

-- One final combined axioms audit on the delivered focused closure.
#print axioms AspisR1.ARV_Adaptive.no_support
#print axioms AspisR1.ARV_AdaptiveAccepted.accepted
#print axioms AspisR1.ARV_AdaptiveChoice.exact
#print axioms AspisR1.ARV_AdaptiveOriginal.original
#print axioms AspisR1.ARV_Constant.no_support
#print axioms AspisR1.ARV_Constant.accepted
#print axioms AspisR1.ARV_Counterexample.accepted_without_support
#print axioms AspisR1.ARV_Filter.eval_runtime
#print axioms AspisR1.ARV_Filter.query_log
#print axioms AspisR1.ARV_FilterCarrier.projection
#print axioms AspisR1.ARV_FilterCarrier.source_view
#print axioms AspisR1.ARV_FilterCharge.issued
#print axioms AspisR1.ARV_FilterCharge.starts
#print axioms AspisR1.ARV_FilterCheckpoint.exact
#print axioms AspisR1.ARV_FilterDomination.pointwise
#print axioms AspisR1.ARV_FilterExact.omitted_iff
#print axioms AspisR1.ARV_FilterJoin.accepted
#print axioms AspisR1.ARV_FilterMass.bounded
#print axioms AspisR1.ARV_FilterNumeric.bounded
#print axioms AspisR1.ARV_FilterOriginal.preserved
#print axioms AspisR1.ARV_FilterPerCoin.extract
#print axioms AspisR1.ARV_FilterPhysical.observed
#print axioms AspisR1.ARV_FilterPreserves.supported
#print axioms AspisR1.ARV_FilterPreserves.rejected
#print axioms AspisR1.ARV_FilterRange.bounded
#print axioms AspisR1.ARV_FilterSupport.accepted
#print axioms AspisR1.ARV_FilterTop.proposed
#print axioms AspisR1.ARV_FilterWeighted.original_law
#print axioms AspisR1.ARV_FirstPartial.accepted
#print axioms AspisR1.ARV_Freeze.original
#print axioms AspisR1.ARV_Fresh.address
#print axioms AspisR1.ARV_LogChange.agrees
#print axioms AspisR1.ARV_NativeCostGap.obstruction
#print axioms AspisR1.ARV_NativePartial.first
#print axioms AspisR1.ARV_NativePartial.second
#print axioms AspisR1.ARV_Nonvacuity.conditional
#print axioms AspisR1.ARV_ObservedSupport.at_eval
#print axioms AspisR1.ARV_OneTuple.obstruction
#print axioms AspisR1.ARV_PaddingChoice.output
#print axioms AspisR1.ARV_PaddingSupport.original
#print axioms AspisR1.ARV_PaddingWork.exact
#print axioms AspisR1.ARV_Poison.snapshot
#print axioms AspisR1.ARV_Poison.sizes
#print axioms AspisR1.ARV_Poison.owned
#print axioms AspisR1.ARV_Poison.invalid
#print axioms AspisR1.ARV_Poison.no_admission
#print axioms AspisR1.ARV_PoisonNative.accepted
#print axioms AspisR1.ARV_UniversalRefutation.from_one_tuple
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.ARV_Root.Proposed
#print axioms AspisR1.SCI_Recovery.model_agreement
#print axioms AspisR1.SCJ_NativeLoaded.entry_loaded

-- Imported trust/work audit only. Zero premise-removal credit.
#print AspisR1.S2W_DigestExtraction.AeneasExtraction
#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall
#print AspisR1.ARS_Coverage.SupportedEntry
#print AspisR1.ARU_Support.At
#print AspisR1.ARU_AllWorld.Supported
#print AspisR1.ARU_CoverageQuantifiers.OriginalCoverage
#print AspisR1.ART_AdversaryWork.work
#print AspisR1.ART_AdversaryWork.Bound
#print AspisR1.FIp_GlobalOwners.Owners
#print AspisR1.ARV_ObservedSupport.Eligible
#check @AspisR1.P6C_Issued.installed
#check @AspisR1.P6C_Whole.same_cuts
#check @AspisR1.ARU_OriginalFactory.original
#check @AspisR1.ARU_OriginalLaw.exact
#print axioms AspisR1.P6C_Issued.installed
#print axioms AspisR1.P6C_Whole.same_cuts
#print axioms AspisR1.ARU_CoverageQuantifiers.exact_iff
