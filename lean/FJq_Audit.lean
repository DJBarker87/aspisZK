import FJn_Audit
import ARX_Root
import ARX_Nonvacuity
import FJq_AcceptedExtra
import FJq_AcceptedLiteralRows
import FJq_AlignedMessages
import FJq_ArbitraryChallengeLiteral
import FJq_ArithmeticInspect
import FJq_ChallengeAlpha
import FJq_ChallengeChi
import FJq_ChallengeEta
import FJq_ChallengeLambda
import FJq_ChallengeLiteral
import FJq_ChallengeMu
import FJq_ChallengeSlots
import FJq_ChallengeTheta
import FJq_ChallengeZc
import FJq_CheckedOffset
import FJq_CircleArray
import FJq_CirclePayload
import FJq_ClaimRead
import FJq_ClaimZero
import FJq_ClaimsLiteralRows
import FJq_ClaimsRoundtrip
import FJq_DecodeChunk
import FJq_DecodeSequence
import FJq_ExtraCanonical
import FJq_ExtraLiteralRows
import FJq_InstallationCondition
import FJq_InstallationFinding
import FJq_LastPhysical
import FJq_LastSource
import FJq_LiteralGamma
import FJq_LiteralOperands
import FJq_LiteralStages
import FJq_LiteralY
import FJq_MainCells
import FJq_MainIndices
import FJq_MaskC1Callback
import FJq_MaskC1Value
import FJq_MaskOnlyCallback
import FJq_MaskOnlyValue
import FJq_MaskedLiteral
import FJq_MaskedMain
import FJq_MaskedSourceFormula
import FJq_OnRunLiteralRows
import FJq_ParentRows
import FJq_ParsedFrames
import FJq_ParsedRows
import FJq_PhysicalPrefix
import FJq_PhysicalRead
import FJq_PreZc
import FJq_PublicField
import FJq_PublicModel
import FJq_PublicNative
import FJq_PublicOnPreparation
import FJq_PublicWire
import FJq_ReferenceMain
import FJq_ReferenceRecord
import FJq_SamplerErasure
import FJq_SamplerStepErasure
import FJq_SourceChallengeMap
import FJq_SourceDecode
import FJq_SourceLiteralClaims
import FJq_SourceLiteralExtra
import FJq_SourceLiteralPublic
import FJq_SourceRecord
import FJq_SourceRowFrame
import FJq_SourceTrace
import FJq_TerminalTransport
set_option autoImplicit false
/-! Focused combined audit of exact checked sources; default pretty-printer limits. -/
#print axioms AspisR1.FJq_AcceptedExtra.value
#print axioms AspisR1.FJq_AcceptedLiteralRows.value
#print axioms AspisR1.FJq_AlignedMessages.value
#print axioms AspisR1.FJq_ArbitraryChallengeLiteral.values
#print axioms AspisR1.FJq_ChallengeAlpha.value
#print axioms AspisR1.FJq_ChallengeChi.value
#print axioms AspisR1.FJq_ChallengeEta.value
#print axioms AspisR1.FJq_ChallengeLambda.value
#print axioms AspisR1.FJq_ChallengeLiteral.values
#print axioms AspisR1.FJq_ChallengeMu.value
#print axioms AspisR1.FJq_ChallengeSlots.length
#print axioms AspisR1.FJq_ChallengeTheta.value
#print axioms AspisR1.FJq_ChallengeZc.value
#print axioms AspisR1.FJq_CheckedOffset.value
#print axioms AspisR1.FJq_CircleArray.value
#print axioms AspisR1.FJq_CirclePayload.value
#print axioms AspisR1.FJq_ClaimRead.value
#print axioms AspisR1.FJq_ClaimZero.value
#print axioms AspisR1.FJq_ClaimsLiteralRows.value
#print axioms AspisR1.FJq_ClaimsRoundtrip.row
#print axioms AspisR1.FJq_DecodeChunk.value
#print axioms AspisR1.FJq_DecodeSequence.value
#print axioms AspisR1.FJq_ExtraCanonical.value
#print axioms AspisR1.FJq_ExtraLiteralRows.value
#print axioms AspisR1.FJq_InstallationCondition.iff_fixed
#print axioms AspisR1.FJq_InstallationCondition.seed_exists
#print axioms AspisR1.FJq_LastPhysical.value
#print axioms AspisR1.FJq_LastSource.value
#print axioms AspisR1.FJq_LiteralGamma.reached
#print axioms AspisR1.FJq_LiteralOperands.value
#print axioms AspisR1.FJq_LiteralStages.reached
#print axioms AspisR1.FJq_LiteralY.reached
#print axioms AspisR1.FJq_MainCells.read
#print axioms AspisR1.FJq_MainCells.bounded
#print axioms AspisR1.FJq_MainCells.point
#print axioms AspisR1.FJq_MainIndices.value
#print axioms AspisR1.FJq_MaskC1Callback.selected
#print axioms AspisR1.FJq_MaskC1Value.value
#print axioms AspisR1.FJq_MaskOnlyCallback.selected
#print axioms AspisR1.FJq_MaskOnlyValue.value
#print axioms AspisR1.FJq_MaskedLiteral.transport
#print axioms AspisR1.FJq_MaskedMain.value
#print axioms AspisR1.FJq_MaskedSourceFormula.value
#print axioms AspisR1.FJq_OnRunLiteralRows.value
#print axioms AspisR1.FJq_ParentRows.reached
#print axioms AspisR1.FJq_ParsedFrames.value
#print axioms AspisR1.FJq_ParsedRows.value
#print axioms AspisR1.FJq_PhysicalPrefix.value
#print axioms AspisR1.FJq_PhysicalRead.value
#print axioms AspisR1.FJq_PreZc.value
#print axioms AspisR1.FJq_PublicField.value
#print axioms AspisR1.FJq_PublicModel.mapped
#print axioms AspisR1.FJq_PublicNative.value
#print axioms AspisR1.FJq_PublicOnPreparation.value
#print axioms AspisR1.FJq_PublicWire.value
#print axioms AspisR1.FJq_ReferenceMain.reached
#print axioms AspisR1.FJq_ReferenceRecord.reached
#print axioms AspisR1.FJq_SamplerErasure.value
#print axioms AspisR1.FJq_SamplerStepErasure.value
#print axioms AspisR1.FJq_SourceChallengeMap.cell
#print axioms AspisR1.FJq_SourceChallengeMap.values
#print axioms AspisR1.FJq_SourceDecode.reached
#print axioms AspisR1.FJq_SourceLiteralClaims.value
#print axioms AspisR1.FJq_SourceLiteralExtra.value
#print axioms AspisR1.FJq_SourceLiteralPublic.value
#print axioms AspisR1.FJq_SourceRecord.reached
#print axioms AspisR1.FJq_SourceRowFrame.value
#print axioms AspisR1.FJq_SourceTrace.value
#print axioms AspisR1.FJq_TerminalTransport.value
#print axioms AspisR1.ARX_Root.deployed
#print axioms AspisR1.ARX_Nonvacuity.conditional
#print axioms AspisR1.FJn_CopyNonvacuity.value
#print axioms AspisR1.FJn_TerminalPartsNonvacuity.value
#check @AspisR1.ARX_Root.deployed
#check @AspisR1.FJq_MaskedMain.value
#check @AspisR1.FJq_MaskedLiteral.transport
#check @AspisR1.FJq_OnRunLiteralRows.value
#check @AspisR1.FJq_ArbitraryChallengeLiteral.values
#check @AspisR1.FJq_LastPhysical.value
#check @AspisR1.FJq_InstallationCondition.iff_fixed
#check @AspisR1.FJq_InstallationCondition.seed_exists
