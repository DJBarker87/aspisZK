import S1CircleCarrierV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCircle
open Aeneas Aeneas.Std Result

def install (B : FinishModel.Boundaries) : FinishModel.Boundaries :=
  {B with circle := S1CircleCarrier.circle}

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Canonical coordinates of the point returned by the same full source
circle-validation call, including its framing and transcript sampling. -/
theorem circle_validated_canonical (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (before after : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord)
    (p : aspis_core.circle.SecureCirclePoint)
    (success : FinishModel.circle_validated (install B) D before record=ok (.Ok p,after)) :
    S1CircleCarrier.Canonical p.x ∧ S1CircleCarrier.Canonical p.y := by
  unfold FinishModel.circle_validated at success
  obtain ⟨row,hrow,success⟩ := bind_success _ _ _ success
  split at success
  all_goals try (cases success)
  all_goals
    obtain ⟨framed,hframed,success⟩ := bind_success _ _ _ success
    obtain ⟨sample,hsample,success⟩ := bind_success _ _ _ success
    rcases sample with ⟨sample,transcript⟩
    cases sample with
    | Err error =>
      change ok (core.result.Result.Err error,transcript)=ok (.Ok p,after) at success
      cases success
    | Ok block =>
      first
      | change (do let scp ← (install B).circle block FinishModel.CircleRow.First
                   ok (core.result.Result.Ok scp,transcript))=ok (.Ok p,after) at success
      | change (do let scp ← (install B).circle block FinishModel.CircleRow.Second
                   ok (core.result.Result.Ok scp,transcript))=ok (.Ok p,after) at success
      obtain ⟨point,hpoint,success⟩ := bind_success _ _ _ success
      have same := Result.ok.inj success
      have hp : point=p := core.result.Result.Ok.inj (congrArg Prod.fst same)
      subst point
      exact S1CircleCarrier.circle_canonical block _ p hpoint

/-- The full finish return supplies both point bounds, without a separate
successful sample or coordinate-range premise. All other semantic leaves in
R and B remain explicit; native circle-callee correspondence remains S9's gate. -/
theorem finish_z_canonical (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (out : r1_semantic.Verified H)
    (success : FinishModel.finish R (S1SemanticRootCopy.install (install B))
      D pub pre before challenges none=ok (.Ok out)) :
    ∀ p ∈ out.z.val, S1CircleCarrier.Canonical p.x ∧ S1CircleCarrier.Canonical p.y := by
  obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,
    hch,hstate,htrans,hclaims,hr25,hextra,hc25,hr26,hbefore,hc26,hz⟩ :=
    S1SemanticFinishBounds.finish_success R (S1SemanticRootCopy.install (install B))
      D pub pre before challenges none out success
  have c0 := circle_validated_canonical (S1SemanticRootCopy.install B) D t25 t26 record25 z0 hc25
  have c1 := circle_validated_canonical (S1SemanticRootCopy.install B) D t26 t27 record26 z1 hc26
  intro p hp
  rw [hz] at hp
  simp only [Array.make, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp
  · subst p; exact c0
  · subst p; exact c1

#print axioms finish_z_canonical
#print axioms circle_validated_canonical
end AspisR1PublicPreparation.S1SemanticCircle
