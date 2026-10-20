import Lean
import CompPoly.Univariate.ToPoly.Impl
import CompPoly.Univariate.EuclideanAlgorithm
import CompPoly.Bivariate.ToPoly
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness
import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness
import CompPoly.Univariate.ToPoly.Degree
import CompPoly.Univariate.Lagrange
import CompPoly.Univariate.Raw.Modular
import CompPoly.Univariate.Raw.Proofs
import CompPoly.Univariate.DivisionCorrectness

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`CompPoly.Univariate.ToPoly.Impl, `CompPoly.Univariate.EuclideanAlgorithm, `CompPoly.Bivariate.ToPoly, `CompPoly.Bivariate.GuruswamiSudan.Interpolation.Dense.Correctness, `CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic, `CompPoly.Univariate.ToPoly.Equiv, `CompPoly.Bivariate.GuruswamiSudan.CoreCorrectness, `CompPoly.Univariate.ToPoly.Degree, `CompPoly.Univariate.Lagrange, `CompPoly.Univariate.Raw.Modular, `CompPoly.Univariate.Raw.Proofs, `CompPoly.Univariate.DivisionCorrectness]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if (`CompPoly).isPrefixOf owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
