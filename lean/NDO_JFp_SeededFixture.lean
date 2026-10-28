import NDO_JFr_ArithmeticFixture
import NDO_JFp_SourceSeed
import NDO_JFp_InitialValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFp_SeededFixture
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem inhabited {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)

    ∃ (expanded y1 : Slice U8) (pre : r1_wire.Prefix)
      (view : AspisR1CurrentCaller.verifier.View) (claims : ClaimsUnrolledFinish.MainClaims)
      (t0 : r1_wire.SemanticTranscript Hash),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
    PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
    expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),y1) ∧ y1.length=928 ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded y1=ok (.Ok view) ∧
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok claims) ∧
    r1_semantic.public_transcript D0 JFs_PublicSerialization.value hash pre.c1_root=ok (.Ok t0) ∧
    t0.next_row.val=0 ∧
    (∃ (t25 : r1_wire.SemanticTranscript Hash) (cs : List (SourceFull25.Call D0 pre)), ∃ r25 r26 z0 t26 z1 t27,
      SourceFull25.Trace D0 pre t0 t25 cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map (fun c => c.record.framed)=pre.records.val.take 25 ∧
      (∀ q ∈ cs.map SourceFull25.Call.q,JFv_RoundArithmetic.Canonical q) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D0 t25 r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D0 t26 r26=ok (.Ok z1,t27) ∧
      t27.next_row.val=27 ∧
      (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
      (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y)) ∧
    (∀ r : Fin 10, ∃ vr,
      r1_wire.Prefix.validated_record pre (JFv_SemanticDecode.roundRow r)=ok (.Ok vr) ∧
      AspisS1ExtractedRoundChildren.decodeMain 28#usize vr 0#usize=ok (.Ok (JFr_RealRounds.polynomial r)) ∧
      AspisS1ExtractedRoundChildren.generatedMainBoundary (JFr_RealRounds.polynomial r)=ok (JFr_RealRounds.running r) ∧
      AspisS1ExtractedRoundChildren.generatedMainValue (JFr_RealRounds.polynomial r)
        (JFr_RealRounds.challenges r) (UScalar.ofNatCore r.val (by have := r.isLt;scalar_tac))=ok (JFr_RealRounds.output r)) ∧
    t0.state=AspisV8R19.SqueezeOracleBridge.encodeState JFr_SeedBoundary.numeric ∧
    r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok JFp_InitialValue.record) ∧
    AspisS1ExtractedRoundChildren.decodeMain 1#usize JFp_InitialValue.record 0#usize=ok (.Ok JFp_InitialValue.values) ∧
    Array.index_usize JFp_InitialValue.values 0#usize=ok JFp_InitialValue.running := by
  obtain ⟨expanded,y1,pre,view,claims,t0,expand,parse,yexpand,length,sourceView,claim,initial,next,oracle,arithmetic⟩ :=
    JFr_ArithmeticFixture.inhabited JFp_SHADigest.digest D B hash
  have seed := JFp_SourceSeed.source D hash expanded pre expand parse
  have same := core.result.Result.Ok.inj (Result.ok.inj (initial.symm.trans seed))
  have state := congrArg r1_wire.SemanticTranscript.state same
  obtain ⟨read,decode,index⟩ := JFp_InitialValue.source expanded pre expand parse
  exact ⟨expanded,y1,pre,view,claims,t0,expand,parse,yexpand,length,sourceView,claim,initial,next,oracle,arithmetic,state,read,decode,index⟩

#print axioms inhabited
end AspisR1.JFp_SeededFixture
end
