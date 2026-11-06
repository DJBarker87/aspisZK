import NJM_RecordDomain
set_option autoImplicit false
namespace AspisR1.NJM_RoundAdmissible
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames

/-- Instrumentation begins at0; no counter-domain assumption is added to the
runtime caller. All mutable source arguments/replies are installed explicitly. -/
theorem returning {H : Type} (D : aspis_core.Digest32 H) (template : RoundPre)
 (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (bound : r.val<10) (record : r1_wire.ValidatedRecord)
 (getter : r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r bound)=ok (.Ok record))
 (p : Polynomial) (b running : Q) (a : Alpha) (before after : r1_wire.SemanticTranscript H)
 (reply : core.result.Result Q r1_wire.Error) (value : Q)
 (call : (PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2=ok (reply,after)) :
 domain (NJM_RoundStage.install {template with count:=0} record p b running a r before after reply value) := by
 have geometry:=NJM_RecordDomain.round (H:=H) bytes pre parsed r bound record getter
 have semantic:=NJM_RecordDomain.semantic D before after record geometry.2.1 reply call
 change r.val<10 ∧ record.framed.val.length≤3717 ∧ 0<252 ∧ True ∧ _
 exact ⟨bound,by omega,by decide,trivial,semantic⟩

/-- A skipped semantic child uses an admissible opaque seed. It is never
entered or used as a success fact. -/
theorem skipped {H : Type} (template : RoundPre)
 (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (bound : r.val<10) (record : r1_wire.ValidatedRecord)
 (getter : r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r bound)=ok (.Ok record))
 (p : Polynomial) (b running : Q) (a : Alpha) (before : r1_wire.SemanticTranscript H) :
 domain (NJM_RoundStage.install {template with count:=0} record p b running a r before before (.Ok aspis_core.field.QM31.ZERO) aspis_core.field.QM31.ZERO) := by
 have geometry:=NJM_RecordDomain.round (H:=H) bytes pre parsed r bound record getter
 change r.val<10 ∧ record.framed.val.length≤3717 ∧ 0<252 ∧ True ∧ True
 exact ⟨bound,by omega,by decide,trivial,trivial⟩

#print axioms returning
#print axioms skipped
end AspisR1.NJM_RoundAdmissible
