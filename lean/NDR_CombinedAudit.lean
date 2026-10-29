import NDO_JHn_TX1Frontier
import NDO_JHn_ExactReturned
import NDO_JHn_Joint
import NDO_JHw_TX2
import NDO_JHx_Instance
import Lean
import RPx_Deployed
import NDO_InstalledIdentity
import NDR_HeadlineNatives
set_option autoImplicit false
open Lean Elab Command


-- Final aggregation: these three declarations retain their exact source bodies.
-- BEGIN verbatim body from NDO_JHq_TX1.lean
set_option autoImplicit false
set_option pp.proofs false
open Lean Elab Command
run_cmd logInfo "NDR_TX1_POST_IMPORT"
noncomputable section
namespace AspisR1.JHq_TX1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
variable [trees : JHe_SHARealization]

-- Named application of the independently checked byte-identity proof.
#check AspisR1.JHn_TX1Frontier.of_byte_identity
#check AspisR1.JHn_ExactReturned.source

theorem accepted1_saved (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first base stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 := by
  exact JHn_TX1Frontier.of_byte_identity base stage JHn_ExactReturned.source
#print axioms accepted1_saved
#check accepted1_saved
end AspisR1.JHq_TX1
end

-- END verbatim body from NDO_JHq_TX1.lean

-- BEGIN verbatim body from NDO_JHw_Joint.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHw_Joint
open Aeneas Aeneas.Std Result
open JHv_Configuration JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHg_World.e1 JHb_World.e1
  JFx_NativeBytes.checkpoint

/-- One saved vector, the original TX1 result, the corrected joint-world TX1
result, and actual TX2 acceptance on the same installed SDK and saved bytes.
The two heaps remain explicit; no equality of those heaps is asserted. -/
theorem source [trees : JHe_SHARealization]
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  obtain ⟨saved,first,identity,length⟩ := JHq_TX1.accepted1_saved (adapter base) stage
  obtain ⟨jointSaved,jointFirst,jointIdentity,_,second⟩ :=
    JHn_Joint.assembleJoint JHn_ExactReturned.source (adapter base) stage
      JHb_DataRequest.value (.Ok slot) (JHw_TX2.accepted2 base stage slot runtime)
  have same : jointSaved=saved := Subtype.ext (jointIdentity.trans identity.symm)
  subst jointSaved
  exact ⟨saved,first,jointFirst,identity,length,second⟩
#print axioms source
set_option pp.proofs false in
#print source
end AspisR1.JHw_Joint
end

-- END verbatim body from NDO_JHw_Joint.lean

-- BEGIN verbatim body from NDO_Joint.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NDO_Joint
#check JHe_SHARealization
open Aeneas Aeneas.Std Result
open JHv_Configuration JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2 JHg_World.e1 JHb_World.e1
  JFx_NativeBytes.checkpoint

/-- One saved vector, the original TX1 result, the corrected joint-world TX1
result, and actual TX2 acceptance on the same installed SDK and saved bytes.
The two heaps remain explicit; no equality of those heaps is asserted. -/
theorem source
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first (JHe_Natives.first (adapter base) stage)
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  exact JHw_Joint.source base stage slot runtime
#print axioms source
set_option pp.proofs false in
#print source
end AspisR1.NDO_Joint
end

-- END verbatim body from NDO_Joint.lean

namespace AspisR1.NDR_CombinedAudit
open Aeneas Aeneas.Std Result

/-- The original joint witness, with both native arguments explicitly presented
through the headline's installed configuration. All fixture/runtime premises and
saved-byte conclusions are retained. -/
theorem sourceOnHeadline
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second
        (AdapterRw.r1_pool_adapter.owned.stage2_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  simpa only [firstNative, secondNative] using NDO_Joint.source base stage slot runtime
#print axioms sourceOnHeadline
end AspisR1.NDR_CombinedAudit

-- Submit only after every NDO witness dependency passes.
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NDO_Joint.source
#print axioms AspisR1.NDO_InstalledIdentity.finalInstalled
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`AspisR1.RPx_Deployed.deployed, `AspisR1.NDO_Joint.source] do
    let some info := env.checked.get.find? root | throwError "missing root {root}"
    let constants := info.type.getUsedConstants
    for required in #[`AspisR1.S2W_D189Wrappers.first, `AspisR1.S2W_D189Wrappers.second] do
      unless constants.contains required do
        throwError "root {root} does not directly mention {required}"
    logInfo m!"NDR_SAME_WRAPPER_CONSTANTS {root}"
  for root in #[`AspisR1.JHq_TX1.accepted1_saved, `AspisR1.JHw_Joint.source] do
    let some info := env.checked.get.find? root | throwError "missing aggregate declaration {root}"
    unless info.type.getUsedConstants.contains `AspisR1.JHe_SHARealization do
      throwError "lost original tree-realization binder in {root}"
    logInfo m!"NDR_TREE_BINDER_RETAINED {root}"
  let some joint := env.checked.get.find? `AspisR1.NDO_Joint.source |
    throwError "missing joint source"
  unless joint.type.getUsedConstants.contains `AspisR1.JHu_FixturePdaRuntime.FixturePdaRuntime do
    throwError "lost fixture runtime premise"
  if joint.type.getUsedConstants.contains `AspisR1.JHe_SHARealization then
    throwError "joint source unexpectedly retains the discharged tree realization"
  logInfo "NDR_JOINT_RUNTIME_PREMISE_RETAINED"
  let imported := env.header.modules.map (·.module)
  for historical in #[
    `AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1,
    `AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyV2,
    `AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw,
    `ExtractedDigest32Begin,
    `ExtractedDigest32Callers,
    `ExtractedSourceDigestOracle,
    `ExtractedSourceFull25Frames,
    `Query31DigestInputBridge,
    `Query31SourceOracleBridge,
    `S2A_InstalledCuts,
    `S2G_InstalledValues,
    `S2K_AfterstateBytes,
    `S2K_AfterstateEncoding,
    `S2K_AfterstateLoop,
    `S2K_AfterstatePrefix,
    `S2K_AfterstatePrepare,
    `S2K_AfterstateStatus,
    `S2K_DigestBytes,
    `S2K_DigestTotal,
    `S2K_Iterator,
    `S2K_LoopStep,
    `S2K_SourcePorts,
    `SemanticRoundAlphaSelectedCanonical,
    `AspisR1CircleSampleWrapper.Funs,
    `AspisR1CircleSampleWrapper.FunsExternal,
    `AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCircleV2,
    `AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1,
    `AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackResultV4,
    `AspisR1CircleSampleWrapper.RawCircleSampleActualSamplerCanonicalV1,
    `AspisR1CircleSampleWrapper.RawCircleSampleActualSecureBridgeV1,
    `AspisR1PoseidonPreparedChannelArraySet,
    `AspisR1PoseidonPreparedChannelNestedSet,
    `AspisR1PoseidonPreparedChannelUpdateInvariantV2,
    `CurrentPreparedAlphaCanonical,
    `CurrentPreparedCandidateSamplers,
    `CurrentPreparedClaimCarriers,
    `CurrentPreparedConcreteBoundaries,
    `CurrentPreparedConcreteQueryRho,
    `CurrentPreparedConcreteRun,
    `CurrentPreparedGammaCallback,
    `CurrentPreparedGammaRank,
    `CurrentPreparedGammaSpecialization,
    `CurrentPreparedInstalledMeaning,
    `CurrentPreparedJointRankMeaning,
    `CurrentPreparedJointRankPrefix,
    `CurrentPreparedJointRankTrace,
    `CurrentPreparedOrdinaryRankV1,
    `CurrentPreparedOriginalPayload,
    `CurrentPreparedPublicSources,
    `CurrentPreparedRhoMeaning,
    `CurrentPreparedScratchMeaning,
    `CurrentPreparedSourceFromQm,
    `CurrentPreparedSourceMeaning,
    `CurrentSamplerOrdinaryCallbackV2,
    `CurrentSamplerPreparedCarrierBoundsV1,
    `ExtractedDigest32SamplerTransport,
    `ExtractedDigest32Transcript,
    `ExtractedSemanticRoundsReachability,
    `ExtractedSourceDigestAddresses,
    `ExtractedTx1Reachability,
    `PreparedFromQmSourceBridge,
    `PreparedParsedInactiveV1,
    `PreparedSourcePowersBoundariesV1,
    `PreparedSourcePowersEntryV1,
    `PreparedSourcePowersJointRankV1,
    `PreparedSourcePowersMeaningV1,
    `Query31ConcreteMaterializedSchedule,
    `Query31ConcreteMaterializedScheduleFull,
    `Query31MathematicalSchedule,
    `RawPoseidonExternalRows,
    `RawPoseidonRowField,
    `S2K_SourceStore,
    `SelectedWideViewInactiveV1,
    `SelectedWideViewPreparedEntryV1,
    `SemanticCallSelectedCanonical,
    `Tx1FinalLenBoundV8
  ] do
    if imported.contains historical then
      throwError "unverified historical provenance object imported: {historical}"
    logInfo m!"NDR_HISTORICAL_OBJECT_EXCLUDED {historical}"
  logInfo m!"NDR_CLOSURE_MODULE_COUNT {env.header.modules.size}"
  logInfo "NDR_COMBINED_COMPLETE"
