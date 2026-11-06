import NJM_RoundAllArgs
import NJM_RoundsInduction
import NJM_RoundsCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundsClosed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames NJG_RoundsCode
abbrev Q := aspis_core.field.QM31

/-- This is the COMPLETE concrete133 packet, not an assumed callback law.
The positive root below proves it at every SAME entered carry. -/
def Child {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) (a : Alpha) (running : Q)
 (r : Usize) (bound : r.val<10) : Prop :=
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
  NJM_RoundAllArgs.Args (NJM_RoundStage.install {template with count:=0} record p b running a r before after reply value) pointer k j z log)

/-- Complete134 native/source composition. Every entered133 child clause is
internally discharged at the SAME carry; the reviewed native cut retains its
full argument, result and frame transcriptions. No operation dictionary or
child equation is a root hypothesis. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) :
 (∃ running,
  PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t)=
  NJM_RoundsInduction.chain native token frame D (PrefixAdapter.fromOld pre) sites
   (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t)) ∧
 (∀ (r : Usize) (member : r∈sites) (carry : Carry H),
  Child D bytes pre parsed carry.2.2 carry.2.1 carry.1 r (NJG_RoundsCode.sites_domain r member)) := by
 refine ⟨NJM_RoundsInduction.rounds native cut token frame D bytes pre parsed t,?_⟩
 intro r member carry
 exact NJM_RoundAllArgs.source D bytes pre parsed carry.2.2 carry.2.1 carry.1 r (NJG_RoundsCode.sites_domain r member)

/-- Local returned-arm invariant, available to136's terminal caller. It does
not add a success or child-result premise to the positive source root. -/
theorem canonical {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
 (carry after : Carry H)
 (success : (NJM_RoundsInduction.chain native token frame D pre sites carry).2=ok (.Ok after)) :
 NJG_CanonicalPrefix.CanonicalBefore after.2.1 10 := by
 rw [NJM_RoundsInduction.source native cut token frame D pre sites carry] at success
 exact NJM_RoundsCanonical.ten D pre carry after success

#print axioms source
#print axioms canonical
end AspisR1.NJM_RoundsClosed
end
