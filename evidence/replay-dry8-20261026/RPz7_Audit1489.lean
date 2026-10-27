import Lean
import RPz7_Op5T_Op3
import RPz7_Op5T_Tx2
import RPz7_Op5T_SuccessAccepted
import RPz7_Op5T_Final
import RPz7_Tx1Q_SameCut
import RPz7_Tx1Q_Initial
import RPz7_Tx1Q_Model
import RPz7_Tx1Q_Control
import RPz7_Tx1Q_Endpoint
import RPz7_Uni_Install
import RPz7_Uni_Cuts
import RPz7_SdkD_FoldedCut
import RPz7_SdkD_PrepareProvenance
import RPz7_SdkD_PrepareCut
import RPz7_SdkD_PhysicalRoots
import RPz7_SdkD_ParserRoot
import RPz7_SdkD_ParserRows
import RPz7_SdkD_SliceAlgebra
import RPz7_SdkD_ModelRoots
import RPz7_SdkD_RootBinding
import RPz7_F3L_PreparedRoots
import RPz7_F3L_AlignedPrefix
import RPz7_F3L_SamplerMessages
import RPz7_F3L_SamplerStatement
import RPz7_F3L_SamplerAligned
import RPz7_F3L_SamplerOrdinary
import RPz7_F3L_OrdinaryReads
import RPz7_PAln_Records
import RPz7_PAln_Ready
import RPz7_PAln_LiteralPrefix
import RPz7_PAln_SubSlice
import RPz7_PAln_OpeningDecode
import RPz7_PAln_RowKappa
import RPz7_PAln_RowFirst
import RPz7_PAln_RowLast
import RPz7_PAln_DataRead
import RPz7_F3L_ModelRead
import RPz7_F3L_OpeningFields
import RPz7_F3K_OpeningFromSource
import RPz7_F3K_RhoOne
import RPz7_F3K_OpeningLast2
import RPz7_F3K_OpeningSuffix
import RPz7_Op4P_Accepted
import RPz7_Tx1Q_Q2Bridge
import RPz7_Tx1Q_Accepted
import RPz7_PSem_Accepted
import RPz7_PAln_Reselect
import RPz7_PAln_SourceRun
import RPz7_PAln_RunFacts
import RPz7_PAln_WhenAligned
import RPz7_PAln_SelectedAccepted
import RPz7_PAln_Public
import RPz7_F3J_Public
import RPz7_F3J_NativeInput
import RPz7_F3J_SamplerStructure
import RPz7_F3J_PrefixWitness
import RPz7_F3J_RunState
import RPz7_F3J_CirclePair
import RPz7_F3J_InitialLog
import RPz7_F3J_InitialValue
import RPz7_F3J_SemanticValue
import RPz7_F3J_SemanticPrefix
import RPz7_F3J_First25
import RPz7_F3J_First27
import RPz7_F3M_SemanticSource
import RPz7_F3M_JoinedClaim
import RPz7_F3L_SemanticInventory
import RPz7_F3M_SamplerPrefix
import RPz7_F3M_OpeningChallenges
import RPz7_F3M_SemanticChallenges
import RPz7_F3M_First25Challenges
import RPz7_F3M_AlphaProjection
import RPz7_F3N_PreparedClaimSource
import RPz7_F3P_SemanticDecode
import RPz7_F3P_ResultBind
import RPz7_F3P_ClaimsTrace
import RPz7_F3P_ClaimsRows
import RPz7_F3P_ClaimsMain
import RPz7_F3P_ClaimsDecode
import RPz7_F3P_ClaimsRecord
import RPz7_F3P_ClaimsMainRows
import RPz7_F3P_SemanticClaims
import RPz7_F3P_SemanticClaimsY
import RPz7_F3P_RecordPacked

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_Op5T_Op3, `RPz7_Op5T_Tx2, `RPz7_Op5T_SuccessAccepted, `RPz7_Op5T_Final, `RPz7_Tx1Q_SameCut, `RPz7_Tx1Q_Initial, `RPz7_Tx1Q_Model, `RPz7_Tx1Q_Control, `RPz7_Tx1Q_Endpoint, `RPz7_Uni_Install, `RPz7_Uni_Cuts, `RPz7_SdkD_FoldedCut, `RPz7_SdkD_PrepareProvenance, `RPz7_SdkD_PrepareCut, `RPz7_SdkD_PhysicalRoots, `RPz7_SdkD_ParserRoot, `RPz7_SdkD_ParserRows, `RPz7_SdkD_SliceAlgebra, `RPz7_SdkD_ModelRoots, `RPz7_SdkD_RootBinding, `RPz7_F3L_PreparedRoots, `RPz7_F3L_AlignedPrefix, `RPz7_F3L_SamplerMessages, `RPz7_F3L_SamplerStatement, `RPz7_F3L_SamplerAligned, `RPz7_F3L_SamplerOrdinary, `RPz7_F3L_OrdinaryReads, `RPz7_PAln_Records, `RPz7_PAln_Ready, `RPz7_PAln_LiteralPrefix, `RPz7_PAln_SubSlice, `RPz7_PAln_OpeningDecode, `RPz7_PAln_RowKappa, `RPz7_PAln_RowFirst, `RPz7_PAln_RowLast, `RPz7_PAln_DataRead, `RPz7_F3L_ModelRead, `RPz7_F3L_OpeningFields, `RPz7_F3K_OpeningFromSource, `RPz7_F3K_RhoOne, `RPz7_F3K_OpeningLast2, `RPz7_F3K_OpeningSuffix, `RPz7_Op4P_Accepted, `RPz7_Tx1Q_Q2Bridge, `RPz7_Tx1Q_Accepted, `RPz7_PSem_Accepted, `RPz7_PAln_Reselect, `RPz7_PAln_SourceRun, `RPz7_PAln_RunFacts, `RPz7_PAln_WhenAligned, `RPz7_PAln_SelectedAccepted, `RPz7_PAln_Public, `RPz7_F3J_Public, `RPz7_F3J_NativeInput, `RPz7_F3J_SamplerStructure, `RPz7_F3J_PrefixWitness, `RPz7_F3J_RunState, `RPz7_F3J_CirclePair, `RPz7_F3J_InitialLog, `RPz7_F3J_InitialValue, `RPz7_F3J_SemanticValue, `RPz7_F3J_SemanticPrefix, `RPz7_F3J_First25, `RPz7_F3J_First27, `RPz7_F3M_SemanticSource, `RPz7_F3M_JoinedClaim, `RPz7_F3L_SemanticInventory, `RPz7_F3M_SamplerPrefix, `RPz7_F3M_OpeningChallenges, `RPz7_F3M_SemanticChallenges, `RPz7_F3M_First25Challenges, `RPz7_F3M_AlphaProjection, `RPz7_F3N_PreparedClaimSource, `RPz7_F3P_SemanticDecode, `RPz7_F3P_ResultBind, `RPz7_F3P_ClaimsTrace, `RPz7_F3P_ClaimsRows, `RPz7_F3P_ClaimsMain, `RPz7_F3P_ClaimsDecode, `RPz7_F3P_ClaimsRecord, `RPz7_F3P_ClaimsMainRows, `RPz7_F3P_SemanticClaims, `RPz7_F3P_SemanticClaimsY, `RPz7_F3P_RecordPacked ]
  let phaseOwners : Array Name := #[ `RPz7_S1SemanticPrefixModelV1, `RPz7_S1SemanticFinishModelV1, `RPz7_S1SemanticFinishBoundsV1, `RPz7_ClaimsUnrolledFinish, `RPz7_S1SemanticVerifyReachabilityV1, `RPz7_S1SemanticFinishRootsV1, `RPz7_S1AcceptedSemanticNumericV1, `RPz7_S1AcceptedChallengesNumericV1, `RPz7_S1SemanticCodeFinishV1, `RPz7_S1SemanticCodeVerifyV1, `RPz7_S1SemanticCodeFinishExactV1, `RPz7_S1SemanticCodeVerifyExactV1, `RPz7_GExp_FinishAssociation, `RPz7_GExp_VerifyAssociation, `RPz7_S1SemanticBudgetV1, `RPz7_AuS1_Semantic3, `RPz7_F3V_SemanticFinish, `RPz7_F3V_SemanticVerify, `RPz7_RawJ_VerifyRead, `RPz7_RawK_VerifyHead, `RPz7_F3U_VerifyHead ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ7_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ7_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ7_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        if phaseOwners.contains owner || n.toString.startsWith "RPz7_PhaseIso" || n.toString == "AspisR1.Rc10_Top.deployed" then
          logInfo m!"RPZ7_KERNEL_TYPE {(Json.mkObj [("name", toJson n.toString), ("type", toJson (repr c.type).pretty)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ7_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ7_AUDIT_COMPLETE declarations={count} modules={selected.size}"
