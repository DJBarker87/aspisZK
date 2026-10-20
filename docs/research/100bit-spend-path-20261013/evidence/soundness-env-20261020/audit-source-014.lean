import Lean
import R0P.Positive
import R0P.PositivityWired
import R0P.CopyConstants
import R0P.Copy
import R0P.PositivityChain
import R0P.Schedule
import R0P.EmptyRoots
import R0P.Digest
import R0P.Semantics
import R0P.SemSource
import R0P.SemView
import R0P.Sumcheck
import R0P.Zerocheck
import R0P.Occupancy
import R0P.Asset
import R0P.LaneMap
import R0P.SemDecision
import R0P.CopyInputLinks
import R0P.Extraction
import R0P.SemAssembly
import R0P.CopyRegistry
import R0P.LogUpFrac
import R0P.LogUpCompress
import R0P.SemBadSets
import R0P.LogUpAssembly
import R0P.LogUpChain
import R0P.SemClosed
import R0P.SemRounds
import R0P.SemD3
import R0P.SemD2

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R0P.Positive, `R0P.PositivityWired, `R0P.CopyConstants, `R0P.Copy, `R0P.PositivityChain, `R0P.Schedule, `R0P.EmptyRoots, `R0P.Digest, `R0P.Semantics, `R0P.SemSource, `R0P.SemView, `R0P.Sumcheck, `R0P.Zerocheck, `R0P.Occupancy, `R0P.Asset, `R0P.LaneMap, `R0P.SemDecision, `R0P.CopyInputLinks, `R0P.Extraction, `R0P.SemAssembly, `R0P.CopyRegistry, `R0P.LogUpFrac, `R0P.LogUpCompress, `R0P.SemBadSets, `R0P.LogUpAssembly, `R0P.LogUpChain, `R0P.SemClosed, `R0P.SemRounds, `R0P.SemD3, `R0P.SemD2]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
