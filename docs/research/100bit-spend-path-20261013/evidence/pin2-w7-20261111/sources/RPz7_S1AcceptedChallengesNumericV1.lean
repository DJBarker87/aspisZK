import RPz7_ActualBeginSelectedCanonical
import RPz7_S1AcceptedSemanticNumericV1
/-! PIN2 W7 (2026-11-11): installed_verify_challenges now takes begin/finish from verify_roots via the new helper accepted_begin_finish_challenges (the body of accepted_verify_challenges after its verify_success step); accepted_verify_challenges (frozen prefix) unchanged; all statements unchanged.  -/
set_option autoImplicit false
namespace AspisS1SemanticArrayRanges
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren

/-- Full four-word ranges for each challenge retained in the complete source
Verified carrier; neither claims nor terminal canonicality is included. -/
def ChallengesNumeric (c : r1_wire.Challenges) : Prop :=
  Canonical c.lambda ∧ Canonical c.chi ∧ Canonical c.theta ∧
  Canonical c.mu ∧ Canonical c.eta ∧ ∀ q ∈ c.zc.val, Canonical q

theorem accepted_verify_challenges {H : Type} (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (accepted : VerifyPrefix.verify (FinishModel.finish children B) D pub bytes hash obs = ok (.Ok out)) :
    ChallengesNumeric out.challenges := by
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    S1SemanticVerify.verify_success _ D pub bytes hash obs out accepted
  obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,
    same,rest⟩ := S1SemanticFinishBounds.finish_success children B D pub pre after challenges obs out finish
  rw [same]
  obtain ⟨hl,hc,ht,hm,he,hz⟩ :=
    ActualBeginSelectedCanonical.begin_challenges_selected_canonical D pre initial after challenges begin
  refine ⟨hl,hc,ht,hm,he,?_⟩
  intro q member
  obtain ⟨i,hi,equal⟩ := List.mem_iff_getElem.mp member
  subst q
  exact hz ⟨i,by simpa [challenges.zc.property] using hi⟩

/-- The begin/finish part of `accepted_verify_challenges`, from the two calls. -/
theorem accepted_begin_finish_challenges {H : Type} (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (initial after : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges) (obs : Option (RPz7_PhaseIso.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (begin : r1_wire.begin D pre initial = ok (.Ok challenges, after))
    (finish : FinishModel.finish children B D pub pre after challenges obs = ok (.Ok out)) :
    ChallengesNumeric out.challenges := by
  obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,
    same,rest⟩ := S1SemanticFinishBounds.finish_success children B D pub pre after challenges obs out finish
  rw [same]
  obtain ⟨hl,hc,ht,hm,he,hz⟩ :=
    ActualBeginSelectedCanonical.begin_challenges_selected_canonical D pre initial after challenges begin
  refine ⟨hl,hc,ht,hm,he,?_⟩
  intro q member
  obtain ⟨i,hi,equal⟩ := List.mem_iff_getElem.mp member
  subst q
  exact hz ⟨i,by simpa [challenges.zc.property] using hi⟩

def CurrentVerifiedChallengesNumeric {H : Type}
    (out : AspisR1CurrentCaller.r1_semantic.Verified H) : Prop :=
  ChallengesNumeric (AspisR1CurrentCaller.InstalledPreparation.retainedSem out).challenges

theorem installed_verify_challenges {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (out : AspisR1CurrentCaller.r1_semantic.Verified H)
    (accepted : AspisR1CurrentCaller.S1SemanticInstallation.verify children B D pub bytes hash = ok (.Ok out)) :
    CurrentVerifiedChallengesNumeric out := by
  obtain ⟨pre,initial,after,challenges,payload,root2,parsed,publicInit,begin,finish,_⟩ :=
    AspisR1CurrentCaller.S1SemanticInstallation.verify_roots children B D pub bytes hash out accepted
  exact accepted_begin_finish_challenges (S1SemanticRootCopy.install B)
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
    (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre initial after challenges none _ begin finish

#print axioms accepted_verify_challenges
#print axioms accepted_begin_finish_challenges
#print axioms installed_verify_challenges
end AspisS1SemanticArrayRanges
