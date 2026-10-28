import NDO_JFv_CirclePair
import NDO_JFv_Sampler25
set_option autoImplicit false
namespace AspisR1.JFv_Sampler27
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem source {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (B : FinishModel.Boundaries) (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
    (initial : t.next_row.val=0) :
    ∃ (t25 : r1_wire.SemanticTranscript H) (cs : List (SourceFull25.Call D pre)), ∃ r25 r26 z0 t26 z1 t27,
      SourceFull25.Trace D pre t t25 cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map (fun c => c.record.framed)=pre.records.val.take 25 ∧
      (∀ q ∈ cs.map SourceFull25.Call.q,JFv_RoundArithmetic.Canonical q) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D t25 r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D t26 r26=ok (.Ok z1,t27) ∧
      t27.next_row.val=27 ∧
      (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
      (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  obtain ⟨t25,qs,run,canonical⟩ := JFv_SemanticChain.success D total pre JFv_Sampler25.rows 0 t initial rfl (by decide)
  have next : t25.next_row.val=25 := by
    have h := (BeginCalls.SemanticRun.carry D pre run).2
    rw [initial] at h
    exact h
  obtain ⟨cs,trace,order,sampled,frames⟩ := SourceFull25.run_full25_frames D pre run (by rfl)
  have order' : cs.map (fun c => c.row.val)=List.range 25 := by
    have h := congrArg (List.map UScalar.val) order
    have values : JFv_Sampler25.rows.map UScalar.val=List.range 25 := rfl
    rw [values] at h
    simpa only [List.map_map,Function.comp_def] using h
  obtain ⟨r25,r26,z0,t26,z1,t27,read25,call25,read26,call26,last,canon0,canon1⟩ :=
    JFv_CirclePair.source D total B pre t25 next
  exact ⟨t25,cs,r25,r26,z0,t26,z1,t27,trace,order',frames,by rw [sampled];exact canonical,
    read25,call25,read26,call26,last,canon0,canon1⟩

#print axioms source
end AspisR1.JFv_Sampler27
