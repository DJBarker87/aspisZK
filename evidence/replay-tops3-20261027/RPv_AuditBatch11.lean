import Lean
import RPv_FJq_SourceDecode
import RPv_FJq_SourceRecord
import RPv_FJq_ClaimsRoundtrip
import RPv_FJq_ReferenceMain
import RPv_FJq_CheckedOffset
import RPv_FJq_DecodeChunk
import RPv_FJq_CirclePayload
import RPv_FJq_DecodeSequence
import RPv_FJq_CircleArray
import RPv_FJq_ClaimsLiteralRows
import RPv_FJq_LiteralStages
import RPv_FJq_LiteralGamma
import RPv_FJq_LiteralY
import RPv_FJq_PhysicalRead
import RPv_FJq_SourceRowFrame
import RPv_FJq_SourceLiteralClaims
import RPv_FJq_ExtraLiteralRows
import RPv_FJq_SourceLiteralExtra
import RPv_FJq_ChallengeSlots
import RPv_FJq_ChallengeLambda
import RPv_FJq_ChallengeChi
import RPv_FJq_ChallengeTheta
import RPv_FJq_ChallengeMu
import RPv_FJq_ChallengeEta
import RPv_FJq_ChallengeZc
import RPv_FJq_PreZc
import RPv_FJq_ChallengeAlpha
import RPv_FJq_LiteralOperands
import RPv_FIr_SourceLast
import RPv_FJq_LastSource
import RPv_FJq_ParsedRows
import RPv_FJq_ParsedFrames
import RPv_FJq_LastPhysical
import RPv_FJt_PrepareHead
import RPv_FJq_AlignedMessages
import RPv_FJt_SamplerHead
import RPv_FJt_PublicLog
import RPv_FJq_PublicField
import RPv_FJq_PublicModel
import RPv_FJq_PublicNative
import RPv_FJq_PublicWire
import RPv_FJq_PublicOnPreparation
import RPv_FJq_SourceLiteralPublic
import RPv_FJa_PublicOnPreparation
import RPv_FJt_PublicJoin
import RPv_FJq_SamplerStepErasure
import RPv_FJq_SamplerErasure
import RPv_FJq_SourceChallengeMap
import RPv_FJq_ChallengeLiteral
import RPv_FJq_ArbitraryChallengeLiteral
import RPv_FJq_PhysicalPrefix
import RPv_FJt_DecodedPublic
import RPv_FJt_CurrentCode
import RPv_FJv_DFinish
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJq_SourceDecode, `RPv_FJq_SourceRecord, `RPv_FJq_ClaimsRoundtrip, `RPv_FJq_ReferenceMain, `RPv_FJq_CheckedOffset, `RPv_FJq_DecodeChunk, `RPv_FJq_CirclePayload, `RPv_FJq_DecodeSequence, `RPv_FJq_CircleArray, `RPv_FJq_ClaimsLiteralRows, `RPv_FJq_LiteralStages, `RPv_FJq_LiteralGamma, `RPv_FJq_LiteralY, `RPv_FJq_PhysicalRead, `RPv_FJq_SourceRowFrame, `RPv_FJq_SourceLiteralClaims, `RPv_FJq_ExtraLiteralRows, `RPv_FJq_SourceLiteralExtra, `RPv_FJq_ChallengeSlots, `RPv_FJq_ChallengeLambda, `RPv_FJq_ChallengeChi, `RPv_FJq_ChallengeTheta, `RPv_FJq_ChallengeMu, `RPv_FJq_ChallengeEta, `RPv_FJq_ChallengeZc, `RPv_FJq_PreZc, `RPv_FJq_ChallengeAlpha, `RPv_FJq_LiteralOperands, `RPv_FIr_SourceLast, `RPv_FJq_LastSource, `RPv_FJq_ParsedRows, `RPv_FJq_ParsedFrames, `RPv_FJq_LastPhysical, `RPv_FJt_PrepareHead, `RPv_FJq_AlignedMessages, `RPv_FJt_SamplerHead, `RPv_FJt_PublicLog, `RPv_FJq_PublicField, `RPv_FJq_PublicModel, `RPv_FJq_PublicNative, `RPv_FJq_PublicWire, `RPv_FJq_PublicOnPreparation, `RPv_FJq_SourceLiteralPublic, `RPv_FJa_PublicOnPreparation, `RPv_FJt_PublicJoin, `RPv_FJq_SamplerStepErasure, `RPv_FJq_SamplerErasure, `RPv_FJq_SourceChallengeMap, `RPv_FJq_ChallengeLiteral, `RPv_FJq_ArbitraryChallengeLiteral, `RPv_FJq_PhysicalPrefix, `RPv_FJt_DecodedPublic, `RPv_FJt_CurrentCode, `RPv_FJv_DFinish ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPV_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPV_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPV_AUDIT_COMPLETE declarations={count} modules={selected.size}"
