import Lean
import Wide.Agreement
import Wide.Factors
import Wide.Smooth
import Wide.Hensel
import Wide.LocalFactors
import Wide.FunctionField
import Wide.PowerSeriesLift
import Wide.RegularWeights
import Wide.RegularRing
import Wide.RegularZeroCount
import Wide.HenselCombinatorics
import Wide.HenselRecurrence
import Wide.RegularEvaluation
import Wide.RegularHensel
import Wide.FactorBudgets
import Wide.HenselWeights
import Wide.HenselIntegralLift
import Wide.HenselSpecialization
import Wide.FiniteBranch
import Wide.BranchEvaluation
import Wide.AmbientCurve
import Wide.FixedBranchCurve
import Wide.ReleasedLift
import Wide.ConcreteBranch
import Wide.OuterSelection
import Wide.FinalRoot
import Wide.FinalBranch
import Wide.FinalSelection
import Wide.FinalCurveBranch
import Wide.FinalCurve

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`Wide.Agreement, `Wide.Factors, `Wide.Smooth, `Wide.Hensel, `Wide.LocalFactors, `Wide.FunctionField, `Wide.PowerSeriesLift, `Wide.RegularWeights, `Wide.RegularRing, `Wide.RegularZeroCount, `Wide.HenselCombinatorics, `Wide.HenselRecurrence, `Wide.RegularEvaluation, `Wide.RegularHensel, `Wide.FactorBudgets, `Wide.HenselWeights, `Wide.HenselIntegralLift, `Wide.HenselSpecialization, `Wide.FiniteBranch, `Wide.BranchEvaluation, `Wide.AmbientCurve, `Wide.FixedBranchCurve, `Wide.ReleasedLift, `Wide.ConcreteBranch, `Wide.OuterSelection, `Wide.FinalRoot, `Wide.FinalBranch, `Wide.FinalSelection, `Wide.FinalCurveBranch, `Wide.FinalCurve]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
