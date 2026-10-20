import Lean
import R1UnifiedInitialCase
import R1UnifiedOpeningRecovery
import R1UnifiedOpeningView
import R1UnifiedOpeningInjection
import R1UnifiedOpeningCase
import R1QueryChainTraceFacts
import R1PrefixQueryTrace
import R1UnifiedQueryInjection
import R1UnifiedQueryCase
import R1JointActualView
import R1UnifiedRhoInjection
import R1UnifiedExperimentInjection
import R1UnifiedRhoCase
import R1UnifiedDispatchCase
import R1UnifiedTotalCase
import RawByteCutTable
import TableLogRepresentative
import RawCutLiteralQueryOrder
import TraceAppend
import OracleProgramLawExt
import R1FollowAppend
import R1TraceAppend

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1UnifiedInitialCase, `R1UnifiedOpeningRecovery, `R1UnifiedOpeningView, `R1UnifiedOpeningInjection, `R1UnifiedOpeningCase, `R1QueryChainTraceFacts, `R1PrefixQueryTrace, `R1UnifiedQueryInjection, `R1UnifiedQueryCase, `R1JointActualView, `R1UnifiedRhoInjection, `R1UnifiedExperimentInjection, `R1UnifiedRhoCase, `R1UnifiedDispatchCase, `R1UnifiedTotalCase, `RawByteCutTable, `TableLogRepresentative, `RawCutLiteralQueryOrder, `TraceAppend, `OracleProgramLawExt, `R1FollowAppend, `R1TraceAppend]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
