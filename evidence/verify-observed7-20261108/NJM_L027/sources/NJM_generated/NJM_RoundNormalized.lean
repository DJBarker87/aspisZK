import NJM_RoundStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundNormalized
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)

/-- All choices below are derived by the checked SAME-argument child join;
there is no supplied operation dictionary or child-output hypothesis. -/
def record {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) (a : NJM_RoundJoin.Alpha) (running : NJM_RoundJoin.Q)
 (r : Usize) (bound : r.val<10) :=
 Classical.choose (NJM_RoundJoin.prepared D bytes pre parsed t a running r bound)

def polynomial {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) (a : NJM_RoundJoin.Alpha) (running : NJM_RoundJoin.Q)
 (r : Usize) (bound : r.val<10) :=
 Classical.choose (Classical.choose_spec (NJM_RoundJoin.prepared D bytes pre parsed t a running r bound))

def boundary {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) (a : NJM_RoundJoin.Alpha) (running : NJM_RoundJoin.Q)
 (r : Usize) (bound : r.val<10) :=
 Classical.choose (Classical.choose_spec (Classical.choose_spec (NJM_RoundJoin.prepared D bytes pre parsed t a running r bound)))

/-- Exact G, including rejection before the semantic child and its full
ordered-effect bind on all other outcomes. -/
def stage {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) (a : NJM_RoundJoin.Alpha) (running : NJM_RoundJoin.Q)
 (r : Usize) (bound : r.val<10) : PreparedHashCode.Log × Result (NJG_RoundCode.Out H) :=
 if boundary D bytes pre parsed t a running r bound≠running then ([],ok (.Err (.Boundary r))) else
 let sem:=run (S1SemanticCode.semanticValidated D t (record D bytes pre parsed t a running r bound))
 NGX_RunBind.appendResult sem.1 sem.2 (NJM_RoundJoin.afterSemantic (polynomial D bytes pre parsed t a running r bound) a r)

/-- No residual child equation occurs among the hypotheses. Every child is
installed at the SAME source arguments by prepared. Native-cut assembly is
separate and not claimed by this source normalization theorem. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) (a : NJM_RoundJoin.Alpha) (running : NJM_RoundJoin.Q)
 (r : Usize) (bound : r.val<10) :
 run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t a running r)=
 stage D bytes pre parsed t a running r bound := by
 exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (NJM_RoundJoin.prepared D bytes pre parsed t a running r bound)))).2.2.2.2.2

#print axioms source
end AspisR1.NJM_RoundNormalized
end
