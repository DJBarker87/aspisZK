import NJM_RoundRoot
import NJM_RoundArgs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundPacket
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames

/-- Positive SAME-source packet: decoder/boundary/value/semantic Results and
all cut domains are derived internally. Source native-cut association lives in
Cases; every returning domain and skipped-child domain is discharged here.
No arbitrary operation dictionary or child-result equation is a hypothesis. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) (a : Alpha) (running : Q)
 (r : Usize) (bound : r.val<10) :
 ∃ (record : r1_wire.ValidatedRecord) (p : Polynomial) (b : Q),
 r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r bound)=ok (.Ok record) ∧
 AspisS1ExtractedRoundChildren.decodeMain 28#usize record 0#usize=ok (.Ok p) ∧
 AspisS1ExtractedRoundChildren.generatedMainBoundary p=ok b ∧
 NJM_RoundRoot.Cases D record p b running a r before
  (PreparedHashCode.run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before a running r)) ∧
 record.row=NJG_RoundProducer.row r bound ∧ record.framed.val.length=901 ∧
 (∀ template,domain (NJM_RoundStage.install {template with count:=0} record p b running a r before before (.Ok aspis_core.field.QM31.ZERO) aspis_core.field.QM31.ZERO)) ∧
 (∀ reply after,(PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2=ok (reply,after) →
  ∀ template value,domain (NJM_RoundStage.install {template with count:=0} record p b running a r before after reply value)) := by
 obtain ⟨record,p,b,getter,decode,boundary,cases⟩:=NJM_RoundRoot.source D bytes pre parsed before a running r bound
 have geometry:=NJM_RecordDomain.round (H:=H) bytes pre parsed r bound record getter
 refine ⟨record,p,b,getter,decode,boundary,cases,geometry.1,geometry.2.2,?_,?_⟩
 · intro template
   exact NJM_RoundAdmissible.skipped template bytes pre parsed r bound record getter p b running a before
 · intro reply after call template value
   exact NJM_RoundAdmissible.returning D template bytes pre parsed r bound record getter p b running a before after reply value call

#print axioms source
end AspisR1.NJM_RoundPacket
end
