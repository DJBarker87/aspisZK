import Lean
import RPz8_SCF_Recovery
import RPz8_ARQ_CommonCuts
import RPz8_ARQ_FrameAgreement
import RPz8_ARQ_FrameReads
import RPz8_ARQ_PrefixRecovery
import RPz8_ARQ_SamplerPrefix
import RPz8_SCH_SourceCuts
import RPz8_SCH_DecodedCuts
import RPz8_SCH_IdealSdkInvoke
import RPz8_SCH_Lower
import RPz8_SCG_CodeMap
import RPz8_SCG_WrapperLog
import RPz8_SCH_WrapperFirst
import RPz8_SCH_OuterFirstIdentity
import RPz8_SCH_SourceFirst
import RPz8_SCH_WrapperSecond
import RPz8_SCH_ChildUpdate
import RPz8_SCH_UpdatePure
import RPz8_SCH_SecondPure
import RPz8_SCH_UpdateRegistry
import RPz8_SCH_UpdateAuthenticate
import RPz8_SCH_UpdateValidate
import RPz8_SCH_SdkSecond
import RPz8_SCH_RangeAt
import RPz8_SCH_OuterSecondIdentity
import RPz8_SCH_SourceSecond
import RPz8_SCG_AcceptedShape
import RPz8_SCG_AcceptedExecution
import RPz8_SCG_AcceptedPair
import RPz8_SCH_AcceptedSources
import RPz8_SCH_AccountCuts
import RPz8_SCE_SnapshotRead
import RPz8_SCE_SuffixShape
import RPz8_SCE_FirstCutBytes
import RPz8_SCE_SubmissionExt
import RPz8_SCH_AccountSubmission
import RPz8_SCH_DecodeAlign
import RPz8_SCH_AccountDecoded
import RPz8_SCE_SecondIndex
import RPz8_SCE_SecondCutBytes
import RPz8_CPH_RecordedKeys
import RPz8_JFx_DataProof00
import RPz8_JFx_DataProof01
import RPz8_JFx_DataProof02
import RPz8_JFx_DataProof03
import RPz8_JFx_DataProof04
import RPz8_JFx_DataProof05
import RPz8_JFx_DataProof06
import RPz8_JFx_DataProof07
import RPz8_JFx_DataProof08
import RPz8_JFx_DataProof09
import RPz8_JFx_DataProof10
import RPz8_JFx_DataProof11
import RPz8_JFx_DataProof12
import RPz8_JFx_DataProof13
import RPz8_JFx_DataProof14
import RPz8_JFx_DataPublic00
import RPz8_JFx_DataCheckpoint00
import RPz8_JFx_NativeBytes
import RPz8_CPR_Separation
import RPz8_CPR_AdmissionGap
import RPz8_SCE_FixtureData
import RPz8_SCE_FixtureGame
import RPz8_SCE_ByteSuffix
import RPz8_SCE_FixtureSubmission
import RPz8_CPH_FixtureData
import RPz8_CPH_FixtureGame
import RPz8_CPH_FixtureKeys
import RPz8_CPH_FixtureEntry
import RPz8_CPH_FixtureAdmission
import RPz8_CPH_FixtureShape
import RPz8_CPH_FixtureReserve
import RPz8_CPH_WrapperConstructor
import RPz8_CPH_FixtureWrappers
import RPz8_CPH_BankSuffix
import RPz8_SCE_FixtureBank
import RPz8_SCE_FixtureAdmission
import RPz8_SCE_FixtureShape
import RPz8_SCE_FixtureReserve
import RPz8_SCE_FixtureWrappers
import RPz8_SCE_FixtureRead
import RPz8_SCI_SameWorld
import RPz8_F3X_PreparedAt
import RPz8_F3X_Aligned
import RPz8_F3X_Canonical
import RPz8_F3X_Join
import RPz8_SCH_RecorderProjection
import RPz8_SCH_CollisionInventory
import RPz8_SCH_TableAfter
import RPz8_SCH_CollisionAppend
import RPz8_SCH_CollisionKnownSuffix
import RPz8_SCH_EventKnownSuffix
import RPz8_SCI_Projection
import RPz8_SCE_SingleRuntime
import RPz8_SCE_ModelReadFrames
import RPz8_SCE_RecoveredExtraction
import RPz8_SCE_ReplayExtractor
import RPz8_SCE_Annotation
import RPz8_SCE_ReplayExtractTransport
import RPz8_SCE_Physical
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_SCF_Recovery, `RPz8_ARQ_CommonCuts, `RPz8_ARQ_FrameAgreement, `RPz8_ARQ_FrameReads, `RPz8_ARQ_PrefixRecovery, `RPz8_ARQ_SamplerPrefix, `RPz8_SCH_SourceCuts, `RPz8_SCH_DecodedCuts, `RPz8_SCH_IdealSdkInvoke, `RPz8_SCH_Lower, `RPz8_SCG_CodeMap, `RPz8_SCG_WrapperLog, `RPz8_SCH_WrapperFirst, `RPz8_SCH_OuterFirstIdentity, `RPz8_SCH_SourceFirst, `RPz8_SCH_WrapperSecond, `RPz8_SCH_ChildUpdate, `RPz8_SCH_UpdatePure, `RPz8_SCH_SecondPure, `RPz8_SCH_UpdateRegistry, `RPz8_SCH_UpdateAuthenticate, `RPz8_SCH_UpdateValidate, `RPz8_SCH_SdkSecond, `RPz8_SCH_RangeAt, `RPz8_SCH_OuterSecondIdentity, `RPz8_SCH_SourceSecond, `RPz8_SCG_AcceptedShape, `RPz8_SCG_AcceptedExecution, `RPz8_SCG_AcceptedPair, `RPz8_SCH_AcceptedSources, `RPz8_SCH_AccountCuts, `RPz8_SCE_SnapshotRead, `RPz8_SCE_SuffixShape, `RPz8_SCE_FirstCutBytes, `RPz8_SCE_SubmissionExt, `RPz8_SCH_AccountSubmission, `RPz8_SCH_DecodeAlign, `RPz8_SCH_AccountDecoded, `RPz8_SCE_SecondIndex, `RPz8_SCE_SecondCutBytes, `RPz8_CPH_RecordedKeys, `RPz8_JFx_DataProof00, `RPz8_JFx_DataProof01, `RPz8_JFx_DataProof02, `RPz8_JFx_DataProof03, `RPz8_JFx_DataProof04, `RPz8_JFx_DataProof05, `RPz8_JFx_DataProof06, `RPz8_JFx_DataProof07, `RPz8_JFx_DataProof08, `RPz8_JFx_DataProof09, `RPz8_JFx_DataProof10, `RPz8_JFx_DataProof11, `RPz8_JFx_DataProof12, `RPz8_JFx_DataProof13, `RPz8_JFx_DataProof14, `RPz8_JFx_DataPublic00, `RPz8_JFx_DataCheckpoint00, `RPz8_JFx_NativeBytes, `RPz8_CPR_Separation, `RPz8_CPR_AdmissionGap, `RPz8_SCE_FixtureData, `RPz8_SCE_FixtureGame, `RPz8_SCE_ByteSuffix, `RPz8_SCE_FixtureSubmission, `RPz8_CPH_FixtureData, `RPz8_CPH_FixtureGame, `RPz8_CPH_FixtureKeys, `RPz8_CPH_FixtureEntry, `RPz8_CPH_FixtureAdmission, `RPz8_CPH_FixtureShape, `RPz8_CPH_FixtureReserve, `RPz8_CPH_WrapperConstructor, `RPz8_CPH_FixtureWrappers, `RPz8_CPH_BankSuffix, `RPz8_SCE_FixtureBank, `RPz8_SCE_FixtureAdmission, `RPz8_SCE_FixtureShape, `RPz8_SCE_FixtureReserve, `RPz8_SCE_FixtureWrappers, `RPz8_SCE_FixtureRead, `RPz8_SCI_SameWorld, `RPz8_F3X_PreparedAt, `RPz8_F3X_Aligned, `RPz8_F3X_Canonical, `RPz8_F3X_Join, `RPz8_SCH_RecorderProjection, `RPz8_SCH_CollisionInventory, `RPz8_SCH_TableAfter, `RPz8_SCH_CollisionAppend, `RPz8_SCH_CollisionKnownSuffix, `RPz8_SCH_EventKnownSuffix, `RPz8_SCI_Projection, `RPz8_SCE_SingleRuntime, `RPz8_SCE_ModelReadFrames, `RPz8_SCE_RecoveredExtraction, `RPz8_SCE_ReplayExtractor, `RPz8_SCE_Annotation, `RPz8_SCE_ReplayExtractTransport, `RPz8_SCE_Physical ]
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
