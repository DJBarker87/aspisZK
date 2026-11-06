import NJM_RoundValue
set_option autoImplicit false
namespace AspisR1.NJM_RoundContinuation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open PreparedHashCode (Code run)

/-- Actual returning semantic child establishes every hypothesis of the value
packet. This is a local branch proof, never a successful-child root assumption. -/
theorem success {H : Type} (D : aspis_core.Digest32 H)
 (record : r1_wire.ValidatedRecord) (before after : r1_wire.SemanticTranscript H)
 (p : NJM_RoundValue.Poly) (a : NJM_RoundValue.Alpha) (r : Usize) (bound : r.val<10)
 (q : NJM_RoundValue.Q)
 (polynomial : ∀ i : Fin 28,JFv_RoundArithmetic.Canonical (FJb_TailCell.cell p i))
 (reply : (run (S1SemanticCode.semanticValidated D before record)).2=ok (.Ok q,after)) :
 ∃ v,generatedMainValue p (a.set r q) r=ok v ∧ JFv_RoundArithmetic.Canonical v ∧
 run (NJM_RoundJoin.afterSemantic p a r (.Ok q,after))=
 ([],ok (.Ok (v,a.set r q,after))) := by
 have qc := NJM_RoundValue.canonical D before after record q reply
 obtain ⟨v,law,vc⟩:=NJM_RoundValue.value p a r bound q qc polynomial
 refine ⟨v,law,vc,?_⟩
 simp only [NJM_RoundJoin.afterSemantic,core.result.Result.Insts.CoreOpsTry.branch,
  NGX_CodeTrace.lift_bind,NJM_RoundValue.update a r bound q,law,NGX_CodeTrace.pure_run]

/-- A rejected semantic child never calls value and keeps no suffix effects. -/
theorem error {H : Type} (p : NJM_RoundValue.Poly) (a : NJM_RoundValue.Alpha)
 (r : Usize) (t : r1_wire.SemanticTranscript H) (e : r1_wire.Error) :
 run (NJM_RoundJoin.afterSemantic p a r (.Err e,t))=([],ok (.Err e)) := rfl

#print axioms success
#print axioms error
end AspisR1.NJM_RoundContinuation
