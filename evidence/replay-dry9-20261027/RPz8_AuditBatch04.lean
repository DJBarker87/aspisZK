import Lean
import RPz8_P2P_Deployed
import RPz8_P2P_Extract
import RPz8_P2P_Source
import RPz8_Rc7_Native
import RPz8_P2P_Result
import RPz8_P2P_R6Result
import RPz8_P2P_Release
import RPz8_P2P_Accounting
import RPz8_FGl_RunFinish
import RPz8_FGl_Aligned
import RPz8_FGl_Canonical
import RPz8_FGl_Join
import RPz8_FGl_CollisionLaw
import RPz8_FGl_Cost
import RPz8_Rc6_Result
import RPz8_F3X_Installation
import RPz8_F3Y_InstalledLaws
import RPz8_FGl_Bound
import RPz8_F3Y_CollisionLaw
import RPz8_F3Y_Cost
import RPz8_F3Y_SourceClaims
import RPz8_F3W_CollisionFree
import RPz8_F3Y_AccountMass
import RPz8_F3U_Numeric
import RPz8_F3X_Margin
import RPz8_F3X_ModelClaims
import RPz8_F3U_RangePolynomial
import RPz8_F3U_RangeEdges
import RPz8_F3U_RangeChord
import RPz8_F3U_Range
import RPz8_FIs_Core
import RPz8_FIn_SourceFinish
import RPz8_FIn_Aligned
import RPz8_FIn_Remaining
import RPz8_FIn_Canonical
import RPz8_FIn_Nonvacuity
import RPz8_FIo_Nonvacuity
import RPz8_FIs_Headline
import RPz8_S6N_Decoder
import RPz8_S6N_Getters
import RPz8_S6N_Installation
import RPz8_FGm_Installation
import RPz8_FGm_Owners
import RPz8_FGm_RunFinish
import RPz8_FGm_Aligned
import RPz8_FGm_Canonical
import RPz8_FGm_Join
import RPz8_FGm_CollisionLaw
import RPz8_FGm_Cost
import RPz8_FGm_Bound
import RPz8_FGm_Headline
import RPz8_Rc8_Top
import RPz8_Rc9_Install
import RPz8_FIp_Core
import RPz8_FIs_Top
import RPz8_FIp_Top
import RPz8_Rc9_Top
import RPz8_Rc10_Top
import RPz8_Rc7_Top
import RPz8_SCH_StageAlign
import RPz8_SCH_InstalledStage
import RPz8_SCC_Physical
import RPz8_SCD_Carrier
import RPz8_SCE_Experiment
import RPz8_SCE_Execution
import RPz8_SCH_IdealSdk
import RPz8_SCH_SdkPure
import RPz8_SCH_DigestAlign
import RPz8_ARQ_Installation
import RPz8_GExp_PartialCount
import RPz8_GExp_ReadPrefix
import RPz8_RPx_AttemptPrefix
import RPz8_ARR_OracleCoverage
import RPz8_ARR_WorldCompatibility
import RPz8_ARR_ReturnCoverage
import RPz8_ARS_QueryTransport
import RPz8_ARU_WrapperAccepted
import RPz8_ARS_QueryCost
import RPz8_ARS_AccountReplay
import RPz8_ARS_NativeAccount
import RPz8_SCE_NativeFirst
import RPz8_SCE_NativeSecond
import RPz8_SCE_AcceptedOutcome
import RPz8_ARU_NativeReplies
import RPz8_ARS_Chronology
import RPz8_ARQ_SemanticJoin
import RPz8_ARQ_SamplerCongr
import RPz8_ARQ_AcceptedRows
import RPz8_ARQ_PreparedSampler
import RPz8_ARQ_RecoveryCanonical
import RPz8_SCE_Projection
import RPz8_ARQ_AccountView
import RPz8_SCE_ReplayTable
import RPz8_SCE_GhostFrames
import RPz8_SCE_ReplayFrames
import RPz8_SCE_ReplayMaps
import RPz8_SCE_ReplayWords
import RPz8_SCF_Cuts
import RPz8_SCF_FrameReplay
import RPz8_SCF_Deletion
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_P2P_Deployed, `RPz8_P2P_Extract, `RPz8_P2P_Source, `RPz8_Rc7_Native, `RPz8_P2P_Result, `RPz8_P2P_R6Result, `RPz8_P2P_Release, `RPz8_P2P_Accounting, `RPz8_FGl_RunFinish, `RPz8_FGl_Aligned, `RPz8_FGl_Canonical, `RPz8_FGl_Join, `RPz8_FGl_CollisionLaw, `RPz8_FGl_Cost, `RPz8_Rc6_Result, `RPz8_F3X_Installation, `RPz8_F3Y_InstalledLaws, `RPz8_FGl_Bound, `RPz8_F3Y_CollisionLaw, `RPz8_F3Y_Cost, `RPz8_F3Y_SourceClaims, `RPz8_F3W_CollisionFree, `RPz8_F3Y_AccountMass, `RPz8_F3U_Numeric, `RPz8_F3X_Margin, `RPz8_F3X_ModelClaims, `RPz8_F3U_RangePolynomial, `RPz8_F3U_RangeEdges, `RPz8_F3U_RangeChord, `RPz8_F3U_Range, `RPz8_FIs_Core, `RPz8_FIn_SourceFinish, `RPz8_FIn_Aligned, `RPz8_FIn_Remaining, `RPz8_FIn_Canonical, `RPz8_FIn_Nonvacuity, `RPz8_FIo_Nonvacuity, `RPz8_FIs_Headline, `RPz8_S6N_Decoder, `RPz8_S6N_Getters, `RPz8_S6N_Installation, `RPz8_FGm_Installation, `RPz8_FGm_Owners, `RPz8_FGm_RunFinish, `RPz8_FGm_Aligned, `RPz8_FGm_Canonical, `RPz8_FGm_Join, `RPz8_FGm_CollisionLaw, `RPz8_FGm_Cost, `RPz8_FGm_Bound, `RPz8_FGm_Headline, `RPz8_Rc8_Top, `RPz8_Rc9_Install, `RPz8_FIp_Core, `RPz8_FIs_Top, `RPz8_FIp_Top, `RPz8_Rc9_Top, `RPz8_Rc10_Top, `RPz8_Rc7_Top, `RPz8_SCH_StageAlign, `RPz8_SCH_InstalledStage, `RPz8_SCC_Physical, `RPz8_SCD_Carrier, `RPz8_SCE_Experiment, `RPz8_SCE_Execution, `RPz8_SCH_IdealSdk, `RPz8_SCH_SdkPure, `RPz8_SCH_DigestAlign, `RPz8_ARQ_Installation, `RPz8_GExp_PartialCount, `RPz8_GExp_ReadPrefix, `RPz8_RPx_AttemptPrefix, `RPz8_ARR_OracleCoverage, `RPz8_ARR_WorldCompatibility, `RPz8_ARR_ReturnCoverage, `RPz8_ARS_QueryTransport, `RPz8_ARU_WrapperAccepted, `RPz8_ARS_QueryCost, `RPz8_ARS_AccountReplay, `RPz8_ARS_NativeAccount, `RPz8_SCE_NativeFirst, `RPz8_SCE_NativeSecond, `RPz8_SCE_AcceptedOutcome, `RPz8_ARU_NativeReplies, `RPz8_ARS_Chronology, `RPz8_ARQ_SemanticJoin, `RPz8_ARQ_SamplerCongr, `RPz8_ARQ_AcceptedRows, `RPz8_ARQ_PreparedSampler, `RPz8_ARQ_RecoveryCanonical, `RPz8_SCE_Projection, `RPz8_ARQ_AccountView, `RPz8_SCE_ReplayTable, `RPz8_SCE_GhostFrames, `RPz8_SCE_ReplayFrames, `RPz8_SCE_ReplayMaps, `RPz8_SCE_ReplayWords, `RPz8_SCF_Cuts, `RPz8_SCF_FrameReplay, `RPz8_SCF_Deletion ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPZ8_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPZ8_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ8_AUDIT_COMPLETE declarations={count} modules={selected.size}"
