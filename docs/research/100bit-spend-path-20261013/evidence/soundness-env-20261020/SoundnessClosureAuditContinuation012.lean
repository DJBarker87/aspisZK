import Lean
import RRConcreteChildModel
import RRConcreteRawStateValidity
import RRBoundedSliceScannerV5
import RRConcreteNormalizeChildTotal
import RRProgramTraversal
import RRProgramMeanTools
import RRConcreteChildrenProgram
import RRConcreteValidState
import RRConcreteInitialValidStateFromFacts
import RRProgramWalkRelation
import RRProgramRecoveryContracts
import RRProgramAbortBound
import RRProgramSequentialContract
import RRProgramQueryBound
import RRSiblingMultiplicityMassV2
import RRReturnedRootMass
import RRConcreteTraversal
import RRConcreteTraversalLaw
import RRConcreteRetryBudget
import RRConcreteRawRecovery
import WideExactNaturalBasisTriangularV4
import WideExactNaturalBasisTriangularV6
import WideExactNaturalBasisTriangularV8
import WideExactNaturalBasisTriangularV9
import WideExactNaturalBasisTriangularV12
import WideExactNaturalBasisTriangularV14
import RRFinalMessageRecovery
import GSActualEncoderGRSBridge
import GSInterpolationRowBasis
import GSConstraintCount

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`RRConcreteChildModel, `RRConcreteRawStateValidity, `RRBoundedSliceScannerV5, `RRConcreteNormalizeChildTotal, `RRProgramTraversal, `RRProgramMeanTools, `RRConcreteChildrenProgram, `RRConcreteValidState, `RRConcreteInitialValidStateFromFacts, `RRProgramWalkRelation, `RRProgramRecoveryContracts, `RRProgramAbortBound, `RRProgramSequentialContract, `RRProgramQueryBound, `RRSiblingMultiplicityMassV2, `RRReturnedRootMass, `RRConcreteTraversal, `RRConcreteTraversalLaw, `RRConcreteRetryBudget, `RRConcreteRawRecovery, `WideExactNaturalBasisTriangularV4, `WideExactNaturalBasisTriangularV6, `WideExactNaturalBasisTriangularV8, `WideExactNaturalBasisTriangularV9, `WideExactNaturalBasisTriangularV12, `WideExactNaturalBasisTriangularV14, `RRFinalMessageRecovery, `GSActualEncoderGRSBridge, `GSInterpolationRowBasis, `GSConstraintCount]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
