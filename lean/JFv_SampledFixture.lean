import JFv_Sampler27
import JFv_ClaimsFixture
import JFv_InitialValue
import JFv_RoundInputs
set_option autoImplicit false
namespace AspisR1.JFv_SampledFixture
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation

/-- Forward calls on one real-byte prefix. The seed is explicit and arbitrary;
public_transcript initialization and arithmetic acceptance gates remain open. -/
theorem inhabited {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (B : FinishModel.Boundaries) (hash : H) :
    ∃ (expanded y1 : Slice U8) (pre : r1_wire.Prefix)
      (view : AspisR1CurrentCaller.verifier.View) (claims : ClaimsUnrolledFinish.MainClaims)
      (t0 : r1_wire.SemanticTranscript H),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
    PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
    expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),y1) ∧ y1.length=928 ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded y1=ok (.Ok view) ∧
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok claims) ∧
    t0.state=pre.c1_root ∧ t0.hash=hash ∧ t0.next_row.val=0 ∧
    (∃ (t25 : r1_wire.SemanticTranscript H) (cs : List (SourceFull25.Call D pre)), ∃ r25 r26 z0 t26 z1 t27,
      SourceFull25.Trace D pre t0 t25 cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map (fun c => c.record.framed)=pre.records.val.take 25 ∧
      (∀ q ∈ cs.map SourceFull25.Call.q,JFv_RoundArithmetic.Canonical q) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D t25 r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D t26 r26=ok (.Ok z1,t27) ∧
      t27.next_row.val=27 ∧
      (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
      (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y)) := by
  obtain ⟨expanded,y1,pre,view,claims,expand,parse,yexpand,length,wide,claim⟩ := JFv_ClaimsFixture.inhabited
  let t0 : r1_wire.SemanticTranscript H := ⟨pre.c1_root,hash,0#u8⟩
  exact ⟨expanded,y1,pre,view,claims,t0,expand,parse,yexpand,length,wide,claim,rfl,rfl,rfl,
    JFv_Sampler27.source D total B pre t0 rfl⟩

#print axioms inhabited
end AspisR1.JFv_SampledFixture
