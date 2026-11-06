import NJM_RoundPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundJoined
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames

/-- Full argument observation, exactly the source coordinates certified by
NIX K073/K074; no opaque reply is interpreted by this predicate. -/
def Calls {H : Type} (template : RoundPre) (record : r1_wire.ValidatedRecord)
 (polynomial : Polynomial) (a : Alpha) (r : Usize)
 (before : r1_wire.SemanticTranscript H) (q : Q) (pointer : Nat)
 (k : Fin 28) (j : Fin 10) (z : Fin 32) (log : RoundLog) : Prop :=
 log.getterPrefix 0=template.prefixToken ∧ log.getterRow 0=15+r.val ∧
 log.getterCount=2 ∧ log.getterPrefix 1=template.prefixToken ∧ log.getterRow 1=15+r.val ∧
 log.decodeRow=15+r.val ∧ log.decodePointer=pointer ∧ log.decodeLength=record.framed.val.length ∧
 log.decodeOffset=0 ∧ log.boundaryValue=cell polynomial k ∧
 log.semanticRow=15+r.val ∧ log.semanticPointer=some pointer ∧
 log.semanticLength=record.framed.val.length ∧ cell log.semanticState z=cell before.state z ∧
 log.semanticNext=before.next_row ∧ log.valuePolynomial=cell polynomial k ∧
 log.valueAlpha=cell (a.set r q) j ∧ log.valueRound=r.val ∧
 log.times 0=0 ∧ log.times 1=1 ∧ log.times 2=2 ∧ log.times 3=3 ∧ log.count=4 ∧ log.frame=template.frame

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
 (∀ (template : RoundPre),domain (NJM_RoundStage.install {template with count:=0} record p b running a r before before (.Ok aspis_core.field.QM31.ZERO) aspis_core.field.QM31.ZERO)) ∧
 (∀ reply after,(PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2=ok (reply,after) →
  ∀ (template : RoundPre) (value : Q),domain (NJM_RoundStage.install {template with count:=0} record p b running a r before after reply value)) ∧
 (∀ (after : r1_wire.SemanticTranscript H) (q : Q),
  (PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2=ok (.Ok q,after) →
  b=running → ∀ (template : RoundPre) (value : Q) (pointer : Nat) (k : Fin 28) (j : Fin 10) (z : Fin 32) (log : RoundLog),
  roundArgs (NJM_RoundStage.install {template with count:=0} record p b running a r before after (.Ok q) value) pointer k j z log →
  Calls template record p a r before q pointer k j z log) := by
 obtain ⟨record,p,b,getter,decode,boundary,cases,row,length,skipped,returning⟩:=
  NJM_RoundPacket.source D bytes pre parsed before a running r bound
 refine ⟨record,p,b,getter,decode,boundary,cases,row,length,skipped,returning,?_⟩
 intro after q semantic same template value pointer k j z log cut
 exact NJM_RoundArgs.success template record p b running same a r bound before after q value pointer k j z log cut

#print axioms source
end AspisR1.NJM_RoundJoined
end
