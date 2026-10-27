import Lean
import RPz7_F3P_RecordParsed
import RPz7_F3P_ClaimField
import RPz7_SAG_FieldRead
import RPz7_FIn_Primitives
import RPz7_SAG_EncodedField
import RPz7_FIn_Horner
import RPz7_FIn_Polynomial
import RPz7_FIn_ExtractInstall
import RPz7_FIn_BodyArithmetic
import RPz7_SdkD_NodeViews
import RPz7_SdkD_FirstPaths
import RPz7_SdkD_WriterCells
import RPz7_CPhy_HeaderCells
import RPz7_SdkD_WriterRoot1
import RPz7_SdkD_WriterSource
import RPz7_SdkD_WriterRoots
import RPz7_Tx2N_Install
import RPz7_Tx2N_Reader
import RPz7_Tx2N_Header
import RPz7_CPhy_Header
import RPz7_Tx2N_Execution
import RPz7_Tx2N_Fields
import RPz7_Tx2N_Query
import RPz7_Tx2N_Twelve
import RPz7_Tx2N_Finish
import RPz7_Tx2N_Reserved
import RPz7_Tx2N_DecodeHeader
import RPz7_Tx2N_Decode
import RPz7_Tx2N_Accepted
import RPz7_SdkD_Inner
import RPz7_SdkD_FirstOrder
import RPz7_SdkD_FirstChild
import RPz7_Op5T_Fixture
import RPz7_Uni_SecondMarks
import RPz7_SdkD_Second
import RPz7_SdkD_Child
import RPz7_SdkD_Marks
import RPz7_Uni_Accepted
import RPz7_SdkD_Uni
import RPz7_SdkD_Accepted
import RPz7_CPhy_Ranges
import RPz7_WAdm_Arithmetic
import RPz7_WAdm_Domain
import RPz7_WAdm_WideIndices
import RPz7_WAdm_WideCarrier
import RPz7_WAdm_Inventory
import RPz7_WAdm_Carrier
import RPz7_WAdm_Fissioned_TypesExternal
import RPz7_WAdm_Fissioned_Types
import RPz7_WAdm_Fissioned_FunsExternal
import RPz7_WAdm_Fissioned_Funs
import RPz7_WAdm_VecStd
import RPz7_WAdm_EmittedScalars
import RPz7_WAdm_Fold
import RPz7_WAdm_LoopShapes
import RPz7_WAdm_ArrayHelpers
import RPz7_WAdm_FissionedContent
import RPz7_WAdm_WeightsHelpers
import RPz7_WAdm_FissionedRoot
import RPz7_WAdm_SourceBody
import RPz7_WAdm_Append
import RPz7_WAdm_FissionedFields
import RPz7_WAdm_BodyJoin
import RPz7_WAdm_SourceWriter
import RPz7_WAdm_NativeInstance
import RPz7_WAdm_Install
import RPz7_WAdm_Execution
import RPz7_WAdm_SameCut
import RPz7_WAdm_RunArithmetic
import RPz7_WAdm_RunControl
import RPz7_WAdm_RunInventory
import RPz7_WAdm_RunDomain
import RPz7_WAdm_ReferenceRun
import RPz7_WAdm_Public
import RPz7_WAdm_Endpoint
import RPz7_WAdm_OriginalEndpoint
import RPz7_WAdm_NativeInstall
import RPz7_WAdm_NativeEndpoint
import RPz7_CPhy_Accepted
import RPz7_CPhy_Physical
import RPz7_T2Nat_Accepted
import RPz7_T2Nat_ReaderJoin
import RPz7_T2Nat_ReaderEffects

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_F3P_RecordParsed, `RPz7_F3P_ClaimField, `RPz7_SAG_FieldRead, `RPz7_FIn_Primitives, `RPz7_SAG_EncodedField, `RPz7_FIn_Horner, `RPz7_FIn_Polynomial, `RPz7_FIn_ExtractInstall, `RPz7_FIn_BodyArithmetic, `RPz7_SdkD_NodeViews, `RPz7_SdkD_FirstPaths, `RPz7_SdkD_WriterCells, `RPz7_CPhy_HeaderCells, `RPz7_SdkD_WriterRoot1, `RPz7_SdkD_WriterSource, `RPz7_SdkD_WriterRoots, `RPz7_Tx2N_Install, `RPz7_Tx2N_Reader, `RPz7_Tx2N_Header, `RPz7_CPhy_Header, `RPz7_Tx2N_Execution, `RPz7_Tx2N_Fields, `RPz7_Tx2N_Query, `RPz7_Tx2N_Twelve, `RPz7_Tx2N_Finish, `RPz7_Tx2N_Reserved, `RPz7_Tx2N_DecodeHeader, `RPz7_Tx2N_Decode, `RPz7_Tx2N_Accepted, `RPz7_SdkD_Inner, `RPz7_SdkD_FirstOrder, `RPz7_SdkD_FirstChild, `RPz7_Op5T_Fixture, `RPz7_Uni_SecondMarks, `RPz7_SdkD_Second, `RPz7_SdkD_Child, `RPz7_SdkD_Marks, `RPz7_Uni_Accepted, `RPz7_SdkD_Uni, `RPz7_SdkD_Accepted, `RPz7_CPhy_Ranges, `RPz7_WAdm_Arithmetic, `RPz7_WAdm_Domain, `RPz7_WAdm_WideIndices, `RPz7_WAdm_WideCarrier, `RPz7_WAdm_Inventory, `RPz7_WAdm_Carrier, `RPz7_WAdm_Fissioned_TypesExternal, `RPz7_WAdm_Fissioned_Types, `RPz7_WAdm_Fissioned_FunsExternal, `RPz7_WAdm_Fissioned_Funs, `RPz7_WAdm_VecStd, `RPz7_WAdm_EmittedScalars, `RPz7_WAdm_Fold, `RPz7_WAdm_LoopShapes, `RPz7_WAdm_ArrayHelpers, `RPz7_WAdm_FissionedContent, `RPz7_WAdm_WeightsHelpers, `RPz7_WAdm_FissionedRoot, `RPz7_WAdm_SourceBody, `RPz7_WAdm_Append, `RPz7_WAdm_FissionedFields, `RPz7_WAdm_BodyJoin, `RPz7_WAdm_SourceWriter, `RPz7_WAdm_NativeInstance, `RPz7_WAdm_Install, `RPz7_WAdm_Execution, `RPz7_WAdm_SameCut, `RPz7_WAdm_RunArithmetic, `RPz7_WAdm_RunControl, `RPz7_WAdm_RunInventory, `RPz7_WAdm_RunDomain, `RPz7_WAdm_ReferenceRun, `RPz7_WAdm_Public, `RPz7_WAdm_Endpoint, `RPz7_WAdm_OriginalEndpoint, `RPz7_WAdm_NativeInstall, `RPz7_WAdm_NativeEndpoint, `RPz7_CPhy_Accepted, `RPz7_CPhy_Physical, `RPz7_T2Nat_Accepted, `RPz7_T2Nat_ReaderJoin, `RPz7_T2Nat_ReaderEffects ]
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
