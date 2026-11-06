import NJM_RoundNormalized
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundRoot
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
open PreparedHashCode (run)
attribute [local instance] Classical.propDecidable
abbrev Q := aspis_core.field.QM31

/-- Reviewed result windows after every child reply has been instantiated at
its SAME arguments. Error/success implications are native cuts, not child laws. -/
def Cases {H : Type} (D : aspis_core.Digest32 H) (record : r1_wire.ValidatedRecord)
 (p : Polynomial) (b running : Q) (a : Alpha) (r : Usize) (before : r1_wire.SemanticTranscript H)
 (whole : PreparedHashCode.Log × Result (NJG_RoundCode.Out H)) : Prop :=
 if b≠running then
  whole=([],ok (.Err (.Boundary r))) ∧
  ∀ (template : RoundPre) (post : RoundOutput),
   (∀ j z,roundResult (NJM_RoundStage.install template record p b running a r before before (.Err .InvalidRow) aspis_core.field.QM31.ZERO) j z post) →
   post=.Err (.Boundary r)
 else
  let child:=run (S1SemanticCode.semanticValidated D before record)
  match child.2 with
  | .fail error => whole=(child.1,.fail error)
  | .div => whole=(child.1,.div)
  | .ok (.Err error,after) =>
    whole=(child.1,ok (.Err error)) ∧
    ∀ (template : RoundPre) (post : RoundOutput),
     (∀ j z,roundResult (NJM_RoundStage.install template record p b running a r before after (.Err error) aspis_core.field.QM31.ZERO) j z post) →
     post=.Err error
  | .ok (.Ok q,after) =>
    ∃ value,AspisS1ExtractedRoundChildren.generatedMainValue p (a.set r q) r=ok value ∧
     JFv_RoundArithmetic.Canonical value ∧
     whole=(child.1,ok (.Ok (value,a.set r q,after))) ∧
     ∀ (template : RoundPre) (post : RoundOutput),
      (∀ j z,roundResult (NJM_RoundStage.install template record p b running a r before after (.Ok q) value) j z post) →
      post=.Ok (value,a.set r q,after.state,after.next_row)

/-- Full concrete133 child/Code/result-cut join. Every child reply equation is
proved internally. The retained arguments are the SAME accepted-prefix domain,
round index, and arbitrary caller transcript/alpha/running. This is source/cut
association; native argument-cut and gate admission remain separate checks. -/
theorem source {H : Type} (D : aspis_core.Digest32 H) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (before : r1_wire.SemanticTranscript H) (a : Alpha) (running : Q)
 (r : Usize) (bound : r.val<10) :
 ∃ (record : r1_wire.ValidatedRecord) (p : Polynomial) (b : Q),
 r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row r bound)=ok (.Ok record) ∧
 AspisS1ExtractedRoundChildren.decodeMain 28#usize record 0#usize=ok (.Ok p) ∧
 AspisS1ExtractedRoundChildren.generatedMainBoundary p=ok b ∧
 Cases D record p b running a r before
  (run (S1SemanticCode.roundStep NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) before a running r)) := by
 obtain ⟨record,p,b,getter,decode,canonical,boundary,bc,normalized⟩:=
  NJM_RoundJoin.prepared D bytes pre parsed before a running r bound
 refine ⟨record,p,b,getter,decode,boundary,?_⟩
 unfold Cases
 by_cases different : b≠running
 · rw [if_pos different]
   constructor
   · simpa only [if_pos different] using normalized
   · intro template post cuts
     exact NJM_RoundNative.boundary _ post p rfl different cuts
 · rw [if_neg different]
   have same : b=running := not_ne_iff.mp different
   have norm := normalized
   rw [if_neg different] at norm
   generalize childEq : run (S1SemanticCode.semanticValidated D before record)=child at norm ⊢
   rcases child with ⟨log,reply⟩
   cases reply with
   | fail error => simpa only [NGX_RunBind.appendResult] using norm
   | div => simpa only [NGX_RunBind.appendResult] using norm
   | ok pair =>
     rcases pair with ⟨sem,after⟩
     cases sem with
     | Err error =>
       constructor
       · simpa only [NGX_RunBind.appendResult,NJM_RoundContinuation.error,List.append_nil] using norm
       · intro template post cuts
         exact NJM_RoundStage.semantic_error template record p b running a r before after error same _ post cuts
     | Ok q =>
       have semEq : (run (S1SemanticCode.semanticValidated D before record)).2=ok (.Ok q,after) := congrArg Prod.snd childEq
       obtain ⟨value,law,vc,cont⟩:=NJM_RoundContinuation.success D record before after p a r bound q canonical semEq
       refine ⟨value,law,vc,?_,?_⟩
       · simpa only [NGX_RunBind.appendResult,cont,List.append_nil] using norm
       · intro template post cuts
         exact NJM_RoundNative.success _ post p q rfl same rfl bound cuts

#print axioms source
end AspisR1.NJM_RoundRoot
end
