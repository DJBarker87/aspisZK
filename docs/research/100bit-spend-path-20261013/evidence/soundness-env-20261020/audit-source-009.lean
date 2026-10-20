import Lean
import Wide.Terminal
import Wide.InitialRoot
import Wide.InitialBranch
import Wide.InitialSelection
import Wide.InitialCurveBranch
import Wide.InitialCurve
import Wide.Initial
import Wide.Instances
import Wide.MatchedInstances
import R0.ListsResponses
import R0.RootCounts
import R0.OpeningWeights
import R0.OpeningDefinitions
import R0.BadSetBounds
import R0.OpeningAlgebra
import R0.FibreRestoration
import Wide.EncoderConjugation
import Wide.SubfieldDescentCore
import Wide.SubfieldDescent
import R0.Binding
import R0.Ledger
import R0.QueryLaw
import R0FS.Verifier
import R0FS.Protocol
import R0FS.Hypotheses
import R0C.OpeningSamplerBounds
import FS2.DuplexDecodes
import R0FS.V2
import R0C.SlackStatement
import R0C.ConcreteSlack

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`Wide.Terminal, `Wide.InitialRoot, `Wide.InitialBranch, `Wide.InitialSelection, `Wide.InitialCurveBranch, `Wide.InitialCurve, `Wide.Initial, `Wide.Instances, `Wide.MatchedInstances, `R0.ListsResponses, `R0.RootCounts, `R0.OpeningWeights, `R0.OpeningDefinitions, `R0.BadSetBounds, `R0.OpeningAlgebra, `R0.FibreRestoration, `Wide.EncoderConjugation, `Wide.SubfieldDescentCore, `Wide.SubfieldDescent, `R0.Binding, `R0.Ledger, `R0.QueryLaw, `R0FS.Verifier, `R0FS.Protocol, `R0FS.Hypotheses, `R0C.OpeningSamplerBounds, `FS2.DuplexDecodes, `R0FS.V2, `R0C.SlackStatement, `R0C.ConcreteSlack]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
