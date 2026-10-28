import NDO_JFu_TranscriptSeed
import NDO_JFv_Sampler27
import NDO_JFv_ClaimsFixture
import NDO_JFv_InitialValue
import NDO_JFv_RoundInputs
set_option autoImplicit false
namespace AspisR1.JFu_InitializedTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation

/-- Source sampling from a genuine semantic public_transcript return.
The supplied semantic public and serializer call are not yet identified with
retained physical public1880 decoding; those remain explicit inputs. -/
theorem inhabited {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (B : FinishModel.Boundaries) (hash : H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (encoded : alloc.vec.Vec U8)
    (serialized : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub=ok (.Ok encoded))
    (length32 : U32)
    (converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len (alloc.vec.Vec.deref encoded))=ok (.Ok length32)) :
    ∃ (expanded y1 : Slice U8) (pre : r1_wire.Prefix)
      (view : AspisR1CurrentCaller.verifier.View) (claims : ClaimsUnrolledFinish.MainClaims)
      (t0 : r1_wire.SemanticTranscript H),
    compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
    PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
    expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),y1) ∧ y1.length=928 ∧
    AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded y1=ok (.Ok view) ∧
    ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) pre=ok (.Ok claims) ∧
    r1_semantic.public_transcript D pub hash pre.c1_root=ok (.Ok t0) ∧
    t0.next_row.val=0 ∧
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
  obtain ⟨t0,initial,next⟩:=JFv_TranscriptInitial.success D total hash (alloc.vec.Vec.deref encoded)
    pre.c1_root length32 converted
  have initialized : r1_semantic.public_transcript D pub hash pre.c1_root=ok (.Ok t0) := by
    unfold r1_semantic.public_transcript
    simp only [serialized,bind_tc_ok,core.result.Result.map_err,
      core.result.Result.Insts.CoreOpsTry.branch]
    exact initial
  exact ⟨expanded,y1,pre,view,claims,t0,expand,parse,yexpand,length,wide,claim,initialized,next,
    JFv_Sampler27.source D total B pre t0 next⟩

#print axioms inhabited
end AspisR1.JFu_InitializedTrace
