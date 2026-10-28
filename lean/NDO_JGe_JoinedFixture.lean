import NDO_JGe_Fixture
import NDO_JGe_SemanticSame
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGe_JoinedFixture
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

/-- Partial SAME-byte fixture. The added root/view facts are unconditional.
The packed-pair continuation remains conditional and no native acceptance or
Rc10 deployed instance is asserted. -/
theorem inhabited {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    let t0 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩
    let t15 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩
    let t25 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩
    ∃ (expanded y1 : Slice U8) (pre : r1_wire.Prefix)
      (view : AspisR1CurrentCaller.verifier.View) (claims : ClaimsUnrolledFinish.MainClaims)
      (cs : List (SourceFull25.Call D0 pre)) (mask : aspis_core.field.QM31)
      (selected : Array FIq_Native.field.QM31 84#usize)
      (a b c : Array FIq_Native.field.QM31 16#usize) (m : Array FIq_Native.field.QM31 10#usize)
      (selectors : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors)
      (sops : FIq_Native.state_only_poseidon.StateOnlyPoseidonSelectors)
      (leading full internal : FIq_Native.field.QM31)
      (schedule path : Array FIq_Native.field.QM31 24#usize)
      (bits : Array FIq_Native.field.QM31 33#usize)
      (sem : Array FIq_Native.field.QM31 24#usize)
      (h1 : FIq_Native.field.QM31)
      (copy : FIq_Native.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1),
    (
    (
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
    PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
    expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),y1) ∧ y1.length=928 ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded y1=ok (.Ok view) ∧
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok claims) ∧
    r1_semantic.public_transcript D0 JFs_PublicSerialization.value hash pre.c1_root=ok (.Ok t0) ∧
    r1_wire.begin D0 pre t0=ok (.Ok JFm_Begin.challenges,t15) ∧
    RoundModel.rounds children D0 pre t15=ok (.Ok
      (genToMain JFr_Data09.output,JFm_PartialAlpha.a10,t25)) ∧
    SourceFull25.Trace D0 pre t0 t25 cs ∧
    cs.map SourceFull25.Call.row=JFm_RealTrace.rows ∧
    cs.map SourceFull25.Call.q=JFm_RealTrace.values ∧
    cs.map (fun c => c.record.framed)=pre.records.val.take 25 ∧
    r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok JFu_Q25Source.record) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0 t25 JFu_Q25Source.record=
      ok (.Ok JFu_CircleExact.z0,(⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok JFu_Q26Source.record) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0
      (⟨encodeState JFu_Q25Source.ratchet,hash,26#u8⟩ : r1_wire.SemanticTranscript Hash) JFu_Q26Source.record=
      ok (.Ok JFu_CircleExact.z1,(⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    FinishModel.pointEq JFu_CircleExact.z0 JFu_CircleExact.z1=ok false ∧
    (SAP_CanonicalCarrier.CanonK JFu_CircleExact.z0.x ∧ SAP_CanonicalCarrier.CanonK JFu_CircleExact.z0.y) ∧
    (SAP_CanonicalCarrier.CanonK JFu_CircleExact.z1.x ∧ SAP_CanonicalCarrier.CanonK JFu_CircleExact.z1.y) ) ∧
    claims=JFu_ClaimsData.claims ∧
    AspisS1ExtractedRoundChildren.decodeMain 29#usize JFu_Q25Source.record 87#usize=ok (.Ok JFu_ClaimsData.a3) ∧
    OraclePortStdBuilder.fromFn 16#usize (FinishModel.closureFn9 D0) claims=ok JFu_MaskInputs.c1 ∧
    OraclePortStdBuilder.fromFn 10#usize (FinishModel.closureFn5 D0) claims=ok JFu_MaskInputs.maskOnly ∧
    FIp_SemanticArithmetic.mask JFu_MaskInputs.c1 JFu_MaskInputs.maskOnly JFu_MaskInputs.g
      JFm_PartialAlpha.a10=ok mask ∧ FIp_SemanticValues.Canon mask ) ∧
    FIq_Native.array_from_fn_copy 84#usize FIq_Native.field.QM31.Insts.CoreMarkerCopy
      FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      FIq_Native.field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.validate_transition JFu_PublicSemantic.value=ok (.Ok ()) ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (FIq_Carriers.toPublic JFs_PublicSerialization.value) JFu_TerminalCallback.claims
      JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges=JFu_TerminalPrefix.tail selected ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts JFu_PublicSemantic.value selected
      JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_TerminalPrefix.challenges.theta=JFy_CompositionTail.tail selected a b c m selectors sops leading full internal path ∧
    FIw_ArrayValue.canonical selected ∧ FIw_ArrayValue.canonical a ∧ FIw_ArrayValue.canonical b ∧
    FIw_ArrayValue.canonical c ∧ FIw_ArrayValue.canonical m ∧
    FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point JFu_TerminalPrefix.alpha=ok selectors ∧
    FIw_ArrayValue.canonical selectors.high ∧ FIw_ArrayValue.canonical selectors.low ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors=ok sops ∧
    FIv_NativeValue.Canon sops.block ∧ FIw_ArrayValue.canonical sops.«local» ∧
    FIq_Native.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,b,c⟩ sops=
      JFy_PoseidonPrefix.tail ⟨a,b,c⟩ sops leading full internal ∧
    FIv_NativeValue.Canon leading ∧ FIv_NativeValue.Canon full ∧ FIv_NativeValue.Canon internal ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
      (Array.repeat 24#usize FIq_Native.field.QM31.ZERO) JFu_PublicSemantic.value ⟨a,b,c⟩ selectors=ok schedule ∧
    FIw_ArrayValue.canonical schedule ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.add_path_lanes schedule ⟨a,b,c⟩ selectors=ok path ∧
    FIw_ArrayValue.canonical path ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.semantic_packed JFu_PublicSemantic.value ⟨a,b,c⟩ selectors=
      JFy_SemanticPrefix.tail JFu_PublicSemantic.value ⟨a,b,c⟩ selectors path ∧
    FIx_ValueBitPrefix.calls ⟨a,b,c⟩ (Array.repeat 33#usize FIq_Native.field.QM31.ZERO)=ok (⟨a,b,c⟩,bits) ∧
    FIw_ArrayValue.canonical bits ∧
    FIw_ArrayValue.decoded bits=FIx_ValueBitPrefix.model ⟨a,b,c⟩
      (FIw_ArrayValue.decoded (Array.repeat 33#usize FIq_Native.field.QM31.ZERO)) ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.semantic_packed JFu_PublicSemantic.value ⟨a,b,c⟩ selectors=ok sem ∧
    FIw_ArrayValue.canonical sem ∧
    FIw_ArrayValue.decoded sem=FIy_NativeCoefficients.model JFu_PublicSemantic.value ⟨a,b,c⟩ selectors ∧
    FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim selected 0#usize 26#usize=ok h1 ∧
    FIq_Native.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1 selectors
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
      JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer=ok copy ∧
    FIv_NativeValue.Canon copy.residual ∧ FIv_NativeValue.Canon copy.active ∧
    JGe_CurrentView.Fields view ∧
    mask = JGd_NumericData.mask ∧
    (∀ terminal, FIp_SemanticValues.Canon terminal →
      (JGb_MaskedArithmetic.run terminal mask = ok JGd_NumericData.running ↔
        terminal = JGd_NumericData.neededTerminal)) ∧
    (JGe_TerminalCondition.Identified → ∃ verified : r1_semantic.Verified Hash,
      FinishModel.finish children JGe_Boundaries.value D0 JFs_PublicSerialization.value pre t15
        JFm_Begin.challenges none=ok (.Ok verified) ∧
      verified.roots=Array.make 2#usize [JFp_InitBytes.root,JFq_Root1.value] ∧
      verified.transcript.state=encodeState JFu_Q26Source.ratchet) ∧
    (∀ (lp fp : Array FIq_Native.field.QM31 4#usize) (ip : Array FIq_Native.field.QM31 16#usize),
      FIq_Native.state_only_poseidon.leading_pair_packed ⟨a,b,c⟩=ok lp →
      FIq_Native.state_only_poseidon.interpolated_full_pair_packed a sops.local=ok fp →
      FIq_Native.state_only_poseidon.interpolated_internal_pair a sops.local=ok ip →
      FIw_ArrayValue.canonical lp → FIw_ArrayValue.canonical fp → FIw_ArrayValue.canonical ip →
      ∃ pos comp g out,
        JFy_PoseidonPrefix.tail ⟨a,b,c⟩ sops leading full internal=ok pos ∧
        FIw_ArrayValue.canonical pos ∧
        FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts JFu_PublicSemantic.value selected
          JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
          JFu_TerminalPrefix.challenges.theta=ok (.Ok (comp,a,m,g,h1,copy.active)) ∧
        FIv_NativeValue.Canon comp ∧ FIv_NativeValue.Canon g ∧
        FIv_NativeValue.decode comp=FIv_CompositionValue.polynomial
          (FIv_NativeValue.decode JFu_TerminalPrefix.challenges.theta) sem pos copy.residual ∧
        FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
          (FIq_Carriers.toPublic JFs_PublicSerialization.value) JFu_TerminalCallback.claims
          JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges=ok (.Ok out) ∧
        FIv_NativeValue.Canon out ∧
        FIv_NativeValue.decode out=FIv_TerminalValue.formula
          (FIv_EqualityValue.weight JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha)
          (FIv_NativeValue.decode comp) (FIv_NativeValue.decode JFu_TerminalPrefix.challenges.mu)
          (FIv_NativeValue.decode h1) (FIv_NativeValue.decode copy.active)) := by
  obtain ⟨expanded,y1,pre,view,claims,cs,mask,selected,a,b,c,m,selectors,sops,leading,full,internal,schedule,path,bits,sem,h1,copy,
    old,gather,validated,native,composition,hselected,hac,hbc,hcc,hmc,hs,hsh,hsl,hps,hpb,hpl,
    projected,hlc,hfc,hic,scheduled,hsc,pathed,hpc,semantic,bitcall,bitcanon,bitvalue,semcall,semcanon,semvalue,h1call,copycall,copycanon,activecanon,fields,sameMask,criterion,tail⟩ := JGe_Fixture.inhabited D B hash
  refine ⟨expanded,y1,pre,view,claims,cs,mask,selected,a,b,c,m,selectors,sops,leading,full,internal,schedule,path,bits,sem,h1,copy,
    old,gather,validated,native,composition,hselected,hac,hbc,hcc,hmc,hs,hsh,hsl,hps,hpb,hpl,
    projected,hlc,hfc,hic,scheduled,hsc,pathed,hpc,semantic,bitcall,bitcanon,bitvalue,semcall,semcanon,semvalue,h1call,copycall,copycanon,activecanon,fields,sameMask,criterion,?_,tail⟩
  intro identified
  exact JGe_SemanticSame.source D hash expanded pre old.1.1 old.1.2.1 identified
#print axioms inhabited
end AspisR1.JGe_JoinedFixture
end
