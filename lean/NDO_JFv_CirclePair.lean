import NDO_JFv_CircleCall
import NDO_JFv_PrefixRecord
set_option autoImplicit false
namespace AspisR1.JFv_CirclePair
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem source {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (B : FinishModel.Boundaries) (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H)
    (initial : t.next_row.val=25) :
    ∃ r25 r26 z0 t26 z1 t27,
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D t r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated (F3M_CircleSource.install B) D t26 r26=ok (.Ok z1,t27) ∧
      t27.next_row.val=27 ∧
      (SAP_CanonicalCarrier.CanonK z0.x ∧ SAP_CanonicalCarrier.CanonK z0.y) ∧
      (SAP_CanonicalCarrier.CanonK z1.x ∧ SAP_CanonicalCarrier.CanonK z1.y) := by
  obtain ⟨r25,read25⟩ := JFv_PrefixRecord.validated pre 25#u8 (by decide)
  have row25 := (SourceFull25.validated_record_bytes pre 25#u8 r25 read25).1
  obtain ⟨z0,t26,call25,next26,canon0⟩ := JFv_CircleCall.source D total B t r25
    (by apply UScalar.eq_of_val_eq;rw [row25];exact initial.symm) (.inl row25)
  have n26 : t26.next_row.val=26 := by rw [row25] at next26;exact next26
  obtain ⟨r26,read26⟩ := JFv_PrefixRecord.validated pre 26#u8 (by decide)
  have row26 := (SourceFull25.validated_record_bytes pre 26#u8 r26 read26).1
  obtain ⟨z1,t27,call26,next27,canon1⟩ := JFv_CircleCall.source D total B t26 r26
    (by apply UScalar.eq_of_val_eq;rw [row26];exact n26.symm) (.inr row26)
  refine ⟨r25,r26,z0,t26,z1,t27,read25,call25,read26,call26,?_,canon0,canon1⟩
  rw [row26] at next27;exact next27

#print axioms source
end AspisR1.JFv_CirclePair
