import SAQ_CompleteTop
import SAQ_Forget
import SAQ_Nonvacuity
set_option autoImplicit false

-- Complete before/after theorem types, including the native extraction and
-- accepted wrappers at their actual selected dictionary.
#check @AspisR1.Rc2_Top.deployed
#check @AspisR1.SAQ_CompleteTop.deployed
#print AspisR1.SAQ_CompleteInstall.select
#print AspisR1.SAQ_CompleteInstall.configuration
#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives
#print AspisR1.Port4C_BasisOuter.SessionABasis
#print AspisR1.Port4C_QueryArithmetic.SessionABackends
#print AspisR1.Port5Q1_NodeModel.SessionAM31
#print AspisR1.Port5Q1_OpeningValues.SessionAS3
#print AspisR1.Port5Q1_GeometryCanonical.SessionAPrimitives
#print AspisR1.Port5Q1_Domain.SessionADomain
#print AspisR1.SAQ_CompleteTen.Outcome
#print AspisR1.SAQ_CompleteCont.Outcome
#print AspisR1.SAQ_CompleteCaller.Outcome
#print AspisR1.SAQ_CompleteResult.Outcome
#check @AspisR1.SAQ_Forget.result
#print AspisR1.SAQ_Constructor.fibre

#print axioms AspisR1.SAQ_CompleteTop.deployed
#print axioms AspisR1.SAQ_CompleteInstall.primitives
#print axioms AspisR1.SAQ_Decoder.primitives
#print axioms AspisR1.SAQ_Constructor.canonical
#print axioms AspisR1.SAQ_Constructor.domain
#print axioms AspisR1.SAQ_Constructor.multiply
#print axioms AspisR1.SAQ_Constructor.one
#print axioms AspisR1.SAQ_Constructor.inverse
#print axioms AspisR1.SAQ_Inverse.source_eq_reference
#print axioms AspisR1.SAQ_LineSource.scale
#print axioms AspisR1.SAQ_LineSource.baseMul
#print axioms AspisR1.SAQ_RawScale.wideScalarEmbedding_eq_algebraMap
#print axioms AspisR1.SAQ_LineJoin.on_cuts
#print axioms AspisR1.SAQ_RecordDecode.successful
#print axioms AspisR1.SAQ_Forget.result
#print axioms AspisR1.SAQ_Nonvacuity.contracts
#print axioms AspisR1.SAQ_Nonvacuity.constructor_partition
#print axioms AspisR1.SAQ_Nonvacuity.inverse_success
