import Lean
import R1TraceValueDecode
import R1CandidateBaseProjection
import R1InputWitness
import R1AppendSemantics
import R1SpendRelationExtraction
import R1ConcreteSpendExtraction
import R1TraceWitnessExtract
import R1ListWitnessExtract
import CandidateListWitnessExtract
import CanonicalCutSemanticRead
import R1CanonicalAddressEmbedding
import CanonicalRawTrace
import CantorZassenhausPair
import CantorZassenhausSplit
import FiniteFieldModularPower
import CantorZassenhausFastTrial
import CantorZassenhausRetries
import CheckedWrappingScalarAgreement
import CompPolyPolynomialBackendBridge
import CompPolySplitTrial
import CompPolySplitRetries
import CompPolySplitFactorQuality
import CompPolyFactorRecursion
import CompPolyFactorCertificate
import FiniteFieldCompleteRootCertificate
import FiniteFieldNormalizedRootFactor
import CompPolyCompleteRoots
import CompPolyFactorOracleProgram
import CompPolyFactorMeanTools
import CompPolyFactorTwoChildBound

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1TraceValueDecode, `R1CandidateBaseProjection, `R1InputWitness, `R1AppendSemantics, `R1SpendRelationExtraction, `R1ConcreteSpendExtraction, `R1TraceWitnessExtract, `R1ListWitnessExtract, `CandidateListWitnessExtract, `CanonicalCutSemanticRead, `R1CanonicalAddressEmbedding, `CanonicalRawTrace, `CantorZassenhausPair, `CantorZassenhausSplit, `FiniteFieldModularPower, `CantorZassenhausFastTrial, `CantorZassenhausRetries, `CheckedWrappingScalarAgreement, `CompPolyPolynomialBackendBridge, `CompPolySplitTrial, `CompPolySplitRetries, `CompPolySplitFactorQuality, `CompPolyFactorRecursion, `CompPolyFactorCertificate, `FiniteFieldCompleteRootCertificate, `FiniteFieldNormalizedRootFactor, `CompPolyCompleteRoots, `CompPolyFactorOracleProgram, `CompPolyFactorMeanTools, `CompPolyFactorTwoChildBound]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
