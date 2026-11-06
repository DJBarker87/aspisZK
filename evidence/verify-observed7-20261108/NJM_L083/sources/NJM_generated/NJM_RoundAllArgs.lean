import NJM_RoundJoined
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundAllArgs
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames

/-- EXACT argument/control/frame assertion body of NIX K073/K074. The
source packet below instantiates this on concrete source replies for EVERY
branch, not merely value-success. The domain is separately derived in Child. -/
def Args (s : RoundPre) (pointer : Nat) (k : Fin 28) (j : Fin 10) (z : Fin 32)
 (p : RoundLog) : Prop :=
 p.getterPrefix 0=s.prefixToken ∧ p.getterRow 0=15+s.round.val ∧
 p.getterCount=(if sampled s then 2 else 1) ∧
 p.getterPrefix 1=(if sampled s then s.prefixToken else 0) ∧
 p.getterRow 1=(if sampled s then 15+s.round.val else 0) ∧
 p.decodeRow=15+s.round.val ∧ p.decodePointer=pointer ∧
 p.decodeLength=s.framed.val.length ∧ p.decodeOffset=0 ∧ p.times 0=s.count ∧ p.frame=s.frame ∧
 p.boundaryValue=polyCell s k ∧ p.times 1=(if decoded s then s.count+1 else s.times 1) ∧
 p.semanticRow=(if sampled s then 15+s.round.val else 0) ∧
 p.semanticPointer=(if sampled s then some pointer else none) ∧
 p.semanticLength=(if sampled s then s.framed.val.length else 0) ∧
 cell p.semanticState z=(if sampled s then cell s.beforeState z else cell s.oldState z) ∧
 p.semanticNext=(if sampled s then s.beforeNext else 0#u8) ∧
 p.times 2=(if sampled s then s.count+2 else s.times 2) ∧
 p.valuePolynomial=(if finished s then polyCell s k else s.seed) ∧
 p.valueAlpha=(if finished s then alphaCell s j else s.seed) ∧
 p.valueRound=(if finished s then s.round.val else 99) ∧
 p.times 3=(if finished s then s.count+3 else s.times 3) ∧
 p.count=s.count+(if !decoded s then 1 else if !decide (s.boundary=s.running) then 2 else
  match s.semantic with | .Err _=>3 | .Ok _=>4)

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
  NJM_RoundJoined.Calls template record p a r before q pointer k j z log) ∧
 (∀ (after : r1_wire.SemanticTranscript H) (reply : core.result.Result Q r1_wire.Error)
  (template : RoundPre) (value : Q) (pointer : Nat) (k : Fin 28) (j : Fin 10) (z : Fin 32) (log : RoundLog),
  roundArgs (NJM_RoundStage.install {template with count:=0} record p b running a r before after reply value) pointer k j z log →
  Args (NJM_RoundStage.install {template with count:=0} record p b running a r before after reply value) pointer k j z log) := by
 obtain ⟨record,p,b,getter,decode,boundary,cases,row,length,skipped,returning,calls⟩:=
  NJM_RoundJoined.source D bytes pre parsed before a running r bound
 refine ⟨record,p,b,getter,decode,boundary,cases,row,length,skipped,returning,calls,?_⟩
 intro after reply template value pointer k j z log cut
 exact cut.2

#print axioms source
end AspisR1.NJM_RoundAllArgs
end
