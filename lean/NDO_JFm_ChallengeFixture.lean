import NDO_JFm_Begin
import NDO_JFm_Rounds
import NDO_JFm_RealTrace
import NDO_JFv_ClaimsFixture
import NDO_JFp_SourceSeed
import NDO_JFv_CirclePair
import NDO_JFv_OracleTotal
set_option autoImplicit false
namespace AspisR1.JFm_ChallengeFixture
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
      (cs : List (SourceFull25.Call D0 pre)), ∃ r25 r26 z0 t26 z1 t27,
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
    r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0 t25 r25=ok (.Ok z0,t26) ∧
    r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
    FinishModel.circle_validated (F3M_CircleSource.install B) D0 t26 r26=ok (.Ok z1,t27) ∧
    t27.next_row.val=27 ∧
    (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
    (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  obtain ⟨expanded,y1,pre,view,claims,expand,parse,yexpand,length,wide,claim⟩ := JFv_ClaimsFixture.inhabited
  let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
    (F3V_OracleDictionary.current JFp_SHADigest.digest D)
  let t25 : r1_wire.SemanticTranscript Hash := ⟨encodeState JFm_Q24Source.ratchet,hash,25#u8⟩
  obtain ⟨cs,trace,rows,values,frames⟩ := JFm_RealTrace.frames D hash expanded pre expand parse
  obtain ⟨r25,r26,z0,t26,z1,t27,read25,call25,read26,call26,next,canon0,canon1⟩ :=
    JFv_CirclePair.source D0 (JFv_OracleTotal.retained JFp_SHADigest.digest D) B pre t25 rfl
  exact ⟨expanded,y1,pre,view,claims,cs,r25,r26,z0,t26,z1,t27,expand,parse,yexpand,length,wide,claim,
    JFp_SourceSeed.source D hash expanded pre expand parse,
    JFm_Begin.source D hash expanded pre expand parse,
    JFm_Rounds.source D hash expanded pre expand parse,
    trace,rows,values,frames,read25,call25,read26,call26,next,canon0,canon1⟩

#print axioms inhabited
end AspisR1.JFm_ChallengeFixture
