import NJM_RoundContinuation
set_option autoImplicit false
namespace AspisR1.NJM_RoundDomainJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Complete source continuation after a SAME semantic execution. Error and
outer abort arms retain their entire original prefixes. This branch statement
is internal support for native cut substitution, not a positive root premise. -/
theorem all {H : Type} (D : aspis_core.Digest32 H)
 (record : r1_wire.ValidatedRecord) (before : r1_wire.SemanticTranscript H)
 (p : NJM_RoundValue.Poly) (a : NJM_RoundValue.Alpha) (r : Usize) (bound : r.val<10)
 (polynomial : ∀ i : Fin 28,JFv_RoundArithmetic.Canonical (FJb_TailCell.cell p i)) :
 match h : (PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2 with
 | .ok (.Ok q,after) =>
   ∃ v,AspisS1ExtractedRoundChildren.generatedMainValue p (a.set r q) r=ok v ∧
    JFv_RoundArithmetic.Canonical v ∧
    PreparedHashCode.run (NJM_RoundJoin.afterSemantic p a r (.Ok q,after))=
     ([],ok (.Ok (v,a.set r q,after)))
 | .ok (.Err error,after) =>
   PreparedHashCode.run (NJM_RoundJoin.afterSemantic p a r (.Err error,after))=([],ok (.Err error))
 | .fail _ => True
 | .div => True := by
 split
 · rename_i q after h
   exact NJM_RoundContinuation.success D record before after p a r bound q polynomial h
 · exact NJM_RoundContinuation.error _ _ _ _ _
 · trivial
 · trivial

#print axioms all
end AspisR1.NJM_RoundDomainJoin
