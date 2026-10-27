import Lean
import RPz8_F3R_PreparationInstall
import RPz8_F3S_ReaderSyntax
import RPz8_F3S_CheckpointSplice
import RPz8_F3S_CheckpointOnRun
import RPz8_F3W_LogJoin
import RPz8_FGl_FinishContinuation
import RPz8_FGl_ModelAcceptance
import RPz8_FGl_AcceptanceValues
import RPz8_FIp_Aligned
import RPz8_FIn_Finish
import RPz8_FIp_Remaining
import RPz8_F3Y_PreparedAt
import RPz8_F3Y_Aligned
import RPz8_F3U_InitCall
import RPz8_F3U_InitAddress
import RPz8_F3U_PublicHead
import RPz8_F3U_VerifyHead
import RPz8_F3U_SemanticHead
import RPz8_F3U_PrepareHead
import RPz8_F3U_LoweredHead
import RPz8_F3U_FirstHead
import RPz8_F3U_OracleHead
import RPz8_F3W_SourceHead
import RPz8_F3T_Semantic
import RPz8_F3T_PublicExt
import RPz8_F3T_ByteTag
import RPz8_F3U_SemanticBytes
import RPz8_F3T_ProofCarriers
import RPz8_F3T_RootAgreement
import RPz8_F3T_AlignedRows
import RPz8_F3T_ParsedRows
import RPz8_F3T_AcceptedParser
import RPz8_F3T_PrefixCongr
import RPz8_F3T_AcceptedReplacement
import RPz8_LogA_Tags
import RPz8_LogA_Dependencies
import RPz8_F3T_InitFrame
import RPz8_F3T_InitHead
import RPz8_F3T_InitialConstructor
import RPz8_F3T_SemanticHead
import RPz8_F3T_HeadCanonical
import RPz8_F3U_CanonicalNative
import RPz8_FGl_Leaves
import RPz8_F3V_ModelAcceptance
import RPz8_F3V_AllWorldRuns
import RPz8_FIp_Canonical
import RPz8_FIp_GlobalOwners
import RPz8_F3V_Leaves
import RPz8_F3Y_Canonical
import RPz8_F3U_RehashValue
import RPz8_F3X_Preparation
import RPz8_F3X_Projection
import RPz8_F3X_Account
import RPz8_F3X_AccountPrior
import RPz8_Hiq_EventExtension
import RPz8_Hiq_CanonicalEvent
import RPz8_F3U_AccountEvent
import RPz8_F3X_Trace
import RPz8_F3X_CollisionErase
import RPz8_F3X_Charge
import RPz8_F3X_SourcePrefix
import RPz8_F3X_ReadInclusion
import RPz8_F3X_SourceBudget
import RPz8_F3X_AccountReads
import RPz8_FIp_Join
import RPz8_F3X_JointCongr
import RPz8_F3U_CollisionJoin
import RPz8_F3U_TwoPass
import RPz8_F3U_UnitMass
import RPz8_F3U_Pointwise
import RPz8_F3U_RuntimePointwise
import RPz8_F3U_Joint
import RPz8_F3U_Averaging
import RPz8_F3U_RuntimeMass
import RPz8_F3U_ConditionalBound
import RPz8_FIp_Bound
import RPz8_F3Y_Join
import RPz8_F3Y_Event
import RPz8_FIp_CollisionLaw
import RPz8_F3U_SourceCost
import RPz8_FIp_Cost
import RPz8_P2P_R3Result
import RPz8_P2P_SafResult
import RPz8_P2P_FinalResult
import RPz8_P2P_R5Close
import RPz8_P2P_ResultSelected
import RPz8_P2P_PairSelected
import RPz8_P2P_ActualResult
import RPz8_P2P_ActualPair
import RPz8_P2P_ClosedResult
import RPz8_P2P_ClosedPair
import RPz8_P2P_DirectResult
import RPz8_P2P_DirectPair
import RPz8_P2P_LiteralResult
import RPz8_P2P_LiteralPair
import RPz8_P2P_LiteralFull
import RPz8_P2P_LiteralTop
import RPz8_P2P_R3Top
import RPz8_P2P_SafTop
import RPz8_P2P_FinalTop
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_F3R_PreparationInstall, `RPz8_F3S_ReaderSyntax, `RPz8_F3S_CheckpointSplice, `RPz8_F3S_CheckpointOnRun, `RPz8_F3W_LogJoin, `RPz8_FGl_FinishContinuation, `RPz8_FGl_ModelAcceptance, `RPz8_FGl_AcceptanceValues, `RPz8_FIp_Aligned, `RPz8_FIn_Finish, `RPz8_FIp_Remaining, `RPz8_F3Y_PreparedAt, `RPz8_F3Y_Aligned, `RPz8_F3U_InitCall, `RPz8_F3U_InitAddress, `RPz8_F3U_PublicHead, `RPz8_F3U_VerifyHead, `RPz8_F3U_SemanticHead, `RPz8_F3U_PrepareHead, `RPz8_F3U_LoweredHead, `RPz8_F3U_FirstHead, `RPz8_F3U_OracleHead, `RPz8_F3W_SourceHead, `RPz8_F3T_Semantic, `RPz8_F3T_PublicExt, `RPz8_F3T_ByteTag, `RPz8_F3U_SemanticBytes, `RPz8_F3T_ProofCarriers, `RPz8_F3T_RootAgreement, `RPz8_F3T_AlignedRows, `RPz8_F3T_ParsedRows, `RPz8_F3T_AcceptedParser, `RPz8_F3T_PrefixCongr, `RPz8_F3T_AcceptedReplacement, `RPz8_LogA_Tags, `RPz8_LogA_Dependencies, `RPz8_F3T_InitFrame, `RPz8_F3T_InitHead, `RPz8_F3T_InitialConstructor, `RPz8_F3T_SemanticHead, `RPz8_F3T_HeadCanonical, `RPz8_F3U_CanonicalNative, `RPz8_FGl_Leaves, `RPz8_F3V_ModelAcceptance, `RPz8_F3V_AllWorldRuns, `RPz8_FIp_Canonical, `RPz8_FIp_GlobalOwners, `RPz8_F3V_Leaves, `RPz8_F3Y_Canonical, `RPz8_F3U_RehashValue, `RPz8_F3X_Preparation, `RPz8_F3X_Projection, `RPz8_F3X_Account, `RPz8_F3X_AccountPrior, `RPz8_Hiq_EventExtension, `RPz8_Hiq_CanonicalEvent, `RPz8_F3U_AccountEvent, `RPz8_F3X_Trace, `RPz8_F3X_CollisionErase, `RPz8_F3X_Charge, `RPz8_F3X_SourcePrefix, `RPz8_F3X_ReadInclusion, `RPz8_F3X_SourceBudget, `RPz8_F3X_AccountReads, `RPz8_FIp_Join, `RPz8_F3X_JointCongr, `RPz8_F3U_CollisionJoin, `RPz8_F3U_TwoPass, `RPz8_F3U_UnitMass, `RPz8_F3U_Pointwise, `RPz8_F3U_RuntimePointwise, `RPz8_F3U_Joint, `RPz8_F3U_Averaging, `RPz8_F3U_RuntimeMass, `RPz8_F3U_ConditionalBound, `RPz8_FIp_Bound, `RPz8_F3Y_Join, `RPz8_F3Y_Event, `RPz8_FIp_CollisionLaw, `RPz8_F3U_SourceCost, `RPz8_FIp_Cost, `RPz8_P2P_R3Result, `RPz8_P2P_SafResult, `RPz8_P2P_FinalResult, `RPz8_P2P_R5Close, `RPz8_P2P_ResultSelected, `RPz8_P2P_PairSelected, `RPz8_P2P_ActualResult, `RPz8_P2P_ActualPair, `RPz8_P2P_ClosedResult, `RPz8_P2P_ClosedPair, `RPz8_P2P_DirectResult, `RPz8_P2P_DirectPair, `RPz8_P2P_LiteralResult, `RPz8_P2P_LiteralPair, `RPz8_P2P_LiteralFull, `RPz8_P2P_LiteralTop, `RPz8_P2P_R3Top, `RPz8_P2P_SafTop, `RPz8_P2P_FinalTop ]
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
