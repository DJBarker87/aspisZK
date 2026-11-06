import NJG_Comparisons
import NJG_CanonicalPrefix
import NJG_RoundResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open PreparedHashCode (Code run)
attribute [local instance] Classical.propDecidable
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Poly := Array Q 28#usize
abbrev R : RoundModel.Boundaries := generatedRoundBoundaries decodeMain

/-- The original continuation with the concrete CLOSED value child installed.
No operation dictionary is exposed to a consumer. -/
def afterSemantic {H : Type} (p : Poly) (a : Alpha) (r : Usize)
 (pair : core.result.Result Q r1_wire.Error × r1_wire.SemanticTranscript H) :
 Code (NJG_RoundCode.Out H) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch pair.1
 match cf with
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (Q × Alpha × r1_wire.SemanticTranscript H) (core.convert.FromSame r1_wire.Error) residual
 | .Continue q =>
   let updated ← Array.update a r q
   let value ← generatedMainValue p updated r
   pure (.Ok (value,updated,pair.2))

/-- Complete SAME-record source equation after installing the decoder and
boundary packets, including boundary rejection and every semantic abort prefix.
The semantic and value functions are concrete, not supplied child equations. -/
theorem prepared {H : Type} (D : aspis_core.Digest32 H)
 (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (t : r1_wire.SemanticTranscript H) (a : Alpha) (running : Q)
 (r : Usize) (bound : r.val<10) :
 ∃ (record : r1_wire.ValidatedRecord) (p : Poly) (b : Q),
 r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r bound)=ok (.Ok record) ∧
 decodeMain 28#usize record 0#usize=ok (.Ok p) ∧
 (∀ i : Fin 28,JFv_RoundArithmetic.Canonical (FJb_TailCell.cell p i)) ∧
 generatedMainBoundary p=ok b ∧ JFv_RoundArithmetic.Canonical b ∧
 run (S1SemanticCode.roundStep R D (PrefixAdapter.fromOld pre) t a running r)=
 (if b≠running then ([],ok (.Err (.Boundary r))) else
 NGX_RunBind.appendResult (run (S1SemanticCode.semanticValidated D t record)).1
  (run (S1SemanticCode.semanticValidated D t record)).2 (afterSemantic p a r)) := by
 obtain ⟨record,p,b,getter,decode,canonical,bc,cb⟩ := NJG_RoundDomains.polynomial bytes pre parsed r bound
 refine ⟨record,p,b,getter,decode,canonical,bc,cb,?_⟩
 unfold S1SemanticCode.roundStep
 simp only [R,generatedRoundBoundaries,NJG_RoundProducer.row_add r bound,getter,decode,NGX_CodeTrace.lift_bind,lift,bind_tc_ok,
  core.result.Result.Insts.CoreOpsTry.branch,bc]
 simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,NJG_Comparisons.qm31,bind_tc_ok]
 by_cases ne : b≠running
 · simp only [ne,decide_false,Bool.not_false,if_true,NGX_CodeTrace.pure_run]
 · have eq : b=running := not_ne_iff.mp ne
   simp only [eq,decide_true, Bool.not_true, if_false]
   rw [NGX_RunBind.bind_run]
   rfl

#print axioms prepared
end AspisR1.NJM_RoundJoin
end
