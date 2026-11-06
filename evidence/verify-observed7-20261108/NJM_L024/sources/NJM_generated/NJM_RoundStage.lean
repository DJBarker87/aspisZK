import NJM_RoundNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundStage
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
abbrev Q := aspis_core.field.QM31

/-- SAME-argument instantiation of the native returning oracle inputs. Only
instrumentation tokens, old log cells and frame come from template. -/
def install {H : Type} (template : RoundPre) (record : r1_wire.ValidatedRecord)
 (polynomial : Polynomial) (boundary running : Q) (a : Alpha) (r : Usize)
 (before after : r1_wire.SemanticTranscript H) (semantic : core.result.Result Q r1_wire.Error)
 (value : Q) : RoundPre :=
 {template with framed:=record.framed,round:=r,alpha:=a,running:=running,
  beforeState:=before.state,beforeNext:=before.next_row,
  polynomial:=.Ok polynomial,boundary:=boundary,semantic:=semantic,
  newState:=after.state,newNext:=after.next_row,value:=value}

/-- All native success windows installed with the concrete source child
replies give precisely the source continuation's returned carrier. Internal
branch theorem: source reply/canonicality are discharged at the parent root. -/
theorem returning {H : Type} (D : aspis_core.Digest32 H) (template : RoundPre)
 (record : r1_wire.ValidatedRecord) (p : Polynomial) (b running : Q) (a : Alpha)
 (r : Usize) (bound : r.val<10) (before after : r1_wire.SemanticTranscript H) (q : Q)
 (same : b=running)
 (polynomial : ∀ i : Fin 28,JFv_RoundArithmetic.Canonical (FJb_TailCell.cell p i))
 (semantic : (PreparedHashCode.run (S1SemanticCode.semanticValidated D before record)).2=ok (.Ok q,after)) :
 ∃ value, AspisS1ExtractedRoundChildren.generatedMainValue p (a.set r q) r=ok value ∧
 JFv_RoundArithmetic.Canonical value ∧
 ∀ post,(∀ j z,roundResult (install template record p b running a r before after (.Ok q) value) j z post) →
 post=.Ok (value,a.set r q,after.state,after.next_row) := by
 obtain ⟨value,law,vc,continuation⟩:=NJM_RoundContinuation.success D record before after p a r bound q polynomial semantic
 refine ⟨value,law,vc,?_⟩
 intro post cuts
 exact NJM_RoundNative.success (install template record p b running a r before after (.Ok q) value) post p q rfl same rfl bound cuts

/-- Full error payload and frame are taken from the SAME cut. -/
theorem semantic_error {H : Type} (template : RoundPre)
 (record : r1_wire.ValidatedRecord) (p : Polynomial) (b running : Q) (a : Alpha)
 (r : Usize) (before after : r1_wire.SemanticTranscript H) (e : r1_wire.Error)
 (same : b=running) (value : Q) (post : RoundOutput)
 (cuts : ∀ j z,roundResult (install template record p b running a r before after (.Err e) value) j z post) :
 post=.Err e :=
 NJM_RoundNative.semantic_error _ post p e rfl same rfl cuts

#print axioms returning
#print axioms semantic_error
end AspisR1.NJM_RoundStage
end
