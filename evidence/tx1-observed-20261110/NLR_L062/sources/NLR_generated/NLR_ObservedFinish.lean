import NLR_ObservedSuccess
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_ObservedFinish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- A SAME-source success branch exposes its ACTUAL parsed Prefix, initial
public transcript, post-begin transcript and challenges at the finish call.
This inversion is not a root premise and asserts no independent success. -/
theorem reached (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
 (sem : r1_semantic.Verified H)
 (success : (run (S1SemanticCode.verify F D pub bytes hash none)).2=ok (.Ok sem)) :
 ∃ (p : r1_wire.Prefix) (initial after : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges),
 PrefixAdapter.parseAccepted bytes=ok (.Ok p) ∧
 (run (S1SemanticCode.publicTranscript D pub hash p.c1_root)).2=ok (.Ok initial) ∧
 (run (S1SemanticCode.begin D p initial)).2=ok (.Ok c,after) ∧
 (run (F D pub p after c none)).2=ok (.Ok sem) := by
 have start : (run (NLJ_ObservedDirect.verify F D pub bytes hash)).2=ok (.Ok sem) := by
  rw [NLJ_ObservedDirect.source];exact success
 unfold NLJ_ObservedDirect.verify at start
 obtain ⟨parsed,parsedCall,rest⟩ := NLR_ObservedSuccess.bind_return _ _ _ start
 cases parsed with
 | Err e => cases rest
 | Ok p =>
  rw [NLR_ObservedSuccess.lift_run] at parsedCall
  change (run (PreparedHashCode.bind (S1SemanticCode.publicTranscript D pub hash p.c1_root)
   (NLJ_ObservedDirect.afterPublic F D pub p))).2=ok (.Ok sem) at rest
  obtain ⟨publicReply,publicCall,rest⟩ := NLR_ObservedSuccess.bind_return _ _ _ rest
  cases publicReply with
  | Err e => cases rest
  | Ok initial =>
   change (run (PreparedHashCode.bind (S1SemanticCode.begin D p initial)
    (fun pair => NLJ_ObservedDirect.afterBegin F D pub p pair.2 pair.1))).2=ok (.Ok sem) at rest
   obtain ⟨beginPair,beginCall,rest⟩ := NLR_ObservedSuccess.bind_return _ _ _ rest
   rcases beginPair with ⟨beginReply,after⟩
   cases beginReply with
   | Err e => cases rest
   | Ok c => exact ⟨p,initial,after,c,parsedCall,publicCall,beginCall,rest⟩
#print axioms reached
set_option pp.proofs false
#print reached
end AspisR1.NLR_ObservedFinish
end
