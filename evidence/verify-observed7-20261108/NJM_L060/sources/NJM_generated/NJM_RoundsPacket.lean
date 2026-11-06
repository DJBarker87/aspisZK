import NJM_RoundPacket
import NJM_RoundsStart
import NJM_RoundsNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundsPacket
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NJG_RoundsCode
open PreparedHashCode (run)
attribute [local irreducible] NJG_RoundsCode.chain

/-- Original ten-call source with the concrete133 interpretation at every
SAME carry. Initial row14 and all child Results are derived, not hypotheses.
The normalized chain retains every rejection/error/abort prefix. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) :
 ∃ running,
 run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t)=
 NJM_RoundsJoin.chain D bytes pre parsed sites
  (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t) ∧
 NJM_RoundsInvariant.Inv 0 (running,Array.repeat 10#usize aspis_core.field.QM31.ZERO,t) := by
 have parse : PrefixAdapter.parseAccepted bytes=ok (.Ok (PrefixAdapter.fromOld pre)) := by
  simp only [PrefixAdapter.parseAccepted,parsed,bind_tc_ok]
 obtain ⟨record,values,getter,decode⟩:=JFv_SemanticDecode.initial bytes (PrefixAdapter.fromOld pre) parse
 obtain ⟨running,index,_⟩:=WP.spec_imp_exists (Array.index_usize_spec values 0#usize (by simp))
 refine ⟨running,?_,NJM_RoundsStart.initial running t⟩
 rw [←NJG_RoundsUnrolled.source]
 simp only [NJG_RoundsCode.source,NJM_RoundJoin.R,AspisS1ExtractedRoundChildren.generatedRoundBoundaries,
  getter,decode,index,NGX_CodeTrace.lift_bind,core.result.Result.Insts.CoreOpsTry.branch]
 exact NJM_RoundsJoin.source D bytes pre parsed sites _

/-- One arbitrary visited site has the complete133 packet at its ACTUAL
arguments. This stronger universal statement is used by the finite SAME-carry
chain above; it does not choose independent executions or posts. -/
theorem entered {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (r : Usize) (member : r∈sites) (carry : Carry H) :
 ∃ (record : r1_wire.ValidatedRecord) (p : NIX_CertificateFrames.Polynomial) (b : NIX_CertificateFrames.Q),
 r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r (NJG_RoundsCode.sites_domain r member))=ok (.Ok record) ∧
 AspisS1ExtractedRoundChildren.decodeMain 28#usize record 0#usize=ok (.Ok p) ∧
 AspisS1ExtractedRoundChildren.generatedMainBoundary p=ok b ∧
 NJM_RoundRoot.Cases D record p b carry.1 carry.2.1 r carry.2.2
  (run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) carry.2.2 carry.2.1 carry.1 r)) :=
 NJM_RoundRoot.source D bytes pre parsed carry.2.2 carry.2.1 carry.1 r (NJG_RoundsCode.sites_domain r member)

#print axioms source
#print axioms entered
end AspisR1.NJM_RoundsPacket
end
