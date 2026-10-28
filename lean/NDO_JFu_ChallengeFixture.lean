import NDO_JFm_ChallengeFixture
import NDO_JFu_CircleExact
import NDO_JFr_PrefixRecords
import NDO_JFr_RecordsAt
set_option autoImplicit false
namespace AspisR1.JFu_ChallengeFixture
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem inhabited {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    let t0 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩
    let t15 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩
    let t25 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩
    ∃ (expanded y1 : Slice U8) (pre : r1_wire.Prefix)
      (view : AspisR1CurrentCaller.verifier.View) (claims : ClaimsUnrolledFinish.MainClaims)
      (cs : List (SourceFull25.Call D0 pre)),
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
    (SAP_CanonicalCarrier.CanonK JFu_CircleExact.z1.x ∧ SAP_CanonicalCarrier.CanonK JFu_CircleExact.z1.y) := by
  obtain ⟨expanded,y1,pre,view,claims,cs,r25,r26,z0,t26,z1,t27,expand,parse,yexpand,length,wide,claim,
    initial,begin,rounds,trace,rows,values,frames,tail⟩ := JFm_ChallengeFixture.inhabited D B hash
  have records := JFr_PrefixRecords.source expanded pre expand parse
  have read25 := JFr_RecordsAt.source pre records 25#u8 (by change 25<27;omega) JFw_NativeRow25.record rfl
  have read26 := JFr_RecordsAt.source pre records 26#u8 (by change 26<27;omega) JFw_NativeRow26.record rfl
  exact ⟨expanded,y1,pre,view,claims,cs,expand,parse,yexpand,length,wide,claim,
    initial,begin,rounds,trace,rows,values,frames,read25,JFu_CircleExact.circle25 D B hash,
    read26,JFu_CircleExact.circle26 D B hash,JFu_CircleExact.inequality,
    JFu_CircleExact.canonical25,JFu_CircleExact.canonical26⟩

#print axioms inhabited
end AspisR1.JFu_ChallengeFixture
