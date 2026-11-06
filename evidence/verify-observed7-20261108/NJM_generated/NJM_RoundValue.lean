import NJM_RoundJoin
set_option autoImplicit false
namespace AspisR1.NJM_RoundValue
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open PreparedHashCode (Code run)
abbrev Q := aspis_core.field.QM31
abbrev Alpha := Array Q 10#usize
abbrev Poly := Array Q 28#usize

/-- Local child-domain fact derived from the complete SAME semantic execution.
This successful-arm lemma is internal, not a positive row-root premise. -/
theorem canonical {H : Type} (D : aspis_core.Digest32 H)
 (before after : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) (q : Q)
 (reply : (run (S1SemanticCode.semanticValidated D before record)).2=ok (.Ok q,after)) :
 JFv_RoundArithmetic.Canonical q := by
 have law : r1_wire.SemanticTranscript.semantic_validated D before record=ok (.Ok q,after) := by
  rw [PreparedHashCode.run_value,S1SemanticCode.semanticValidated_erasure] at reply
  exact reply
 exact (NJG_AlphaCarry.canonical_iff q).mpr
  (SemanticCallSelectedCanonical.semantic_success_selected_canonical D before after record q law)

/-- The update is the source writeback and changes precisely the active slot. -/
theorem update (a : Alpha) (r : Usize) (bound : r.val<10) (q : Q) :
 Array.update a r q=ok (a.set r q) := by
 obtain ⟨v,call,hv⟩:=WP.spec_imp_exists (Array.update_spec a r q (by simpa using bound))
 simpa only [hv] using call

/-- Concrete value child is total on the active challenge obtained from the
SAME semantic child. Every other alpha slot is arbitrary. -/
theorem value (p : Poly) (a : Alpha) (r : Usize) (bound : r.val<10) (q : Q)
 (canonical : JFv_RoundArithmetic.Canonical q)
 (polynomial : ∀ i : Fin 28,JFv_RoundArithmetic.Canonical (FJb_TailCell.cell p i)) :
 ∃ v, generatedMainValue p (a.set r q) r=ok v ∧ JFv_RoundArithmetic.Canonical v := by
 apply JFv_RoundArithmetic.value p (a.set r q) r bound
 · change JFv_RoundArithmetic.Canonical (FJb_TailCell.cell (a.set r q) ⟨r.val,by simpa using bound⟩)
   rw [NJG_AlphaCarry.set_selected]
   exact canonical
 · exact polynomial

#print axioms canonical
#print axioms update
#print axioms value
end AspisR1.NJM_RoundValue
