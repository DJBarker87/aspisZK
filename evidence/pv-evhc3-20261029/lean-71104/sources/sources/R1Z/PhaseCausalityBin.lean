import R1Z.PhaseTranscriptBin

set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseCausalityBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.LayoutR1PBin R1Z.TranscriptR1 R1Z.PhaseScheduleBin
  R1Z.PhaseLocalityBin R1Z.PhaseTranscriptBin R1Z.CouplingR1PBin
  R1Z.PremisesR1PBin

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {h : HonestProver K} {B : PackBasis F}
  {outputs : Statement K CommitHandle → Challenges K → Aux}
  {x : Statement K CommitHandle} (W : R1PhaseWire h B outputs x)
  (P : R1PhaseProver h B outputs x W)

theorem commitment_causal (w : h.Instance) (sec : SecP) (d : OracleAnswer)
    (c : CPos P.data.E₁ P.data.E₂) (v v' : Vectors W P)
    (he : StageAgree W P (.inr c) v v') :
    attAddr W.toWire P.toProver h B outputs x w sec d v (.inr c) =
      attAddr W.toWire P.toProver h B outputs x w sec d v' (.inr c) := by
  have hr (q : RIdx) (hq : restStage q < stage (.inr c)) : restOf v q = restOf v' q :=
    he (.inr (.inr (.inr q))) hq
  change gram _ _ _ sec d (restOf v) c = gram _ _ _ sec d (restOf v') c
  rcases c with T | (b | b) | (b | i | ⟨T, u⟩ | ⟨T, u⟩ | ⟨T, n⟩)
  · have hj (j : Fin 2) := hr (rootChild T j) (root_children T j)
    simp only [gram, nodeBytes, hj]
  · have hs := hr (qSeed 0) (by simp [restStage, qSeed, stage])
    simp only [gram, hs]
  · have hs := hr (qSeed 2) (by simp [restStage, qSeed, stage])
    simp only [gram, hs]
  · by_cases hb : b.val = 0
    · simp only [gram, hb, if_pos]
    · have h0 : b.val = 1 := by have := b.isLt; omega
      have hs := hr (qBind 0) (by simp [qBind, restStage, stage, h0])
      simp only [gram, hb, if_false, hs]
  · by_cases hi : i.val = 0
    · have hs := hr (qBind 0) (by simp [qBind, restStage, stage, hi])
      simp only [gram, hi, if_true, hs]
    · by_cases hi1 : i.val = 1
      · have hs := hr (qBind 0) (by simp [qBind, restStage, stage, hi1])
        simp only [gram, hi, hi1, if_false, if_true, hs]
      · have hi2 : i.val = 2 := by have := i.isLt; omega
        have h0 := hr (qBind 1) (by simp [qBind, restStage, stage, hi2])
        have h1 := hr (qSeed 1) (by simp [qSeed, restStage, stage, hi2])
        simp only [gram, hi, hi1, if_false, h0, h1]
  · have hs := hr (qBind 1) (by simp [qBind, restStage, stage])
    simp only [gram, hs]
  · have ht : 5 < stage (.inr (.inr (.inr (qLeaf T u))) : Pos1 P.data.E₁ P.data.E₂) := by
      simp [stage, qLeaf, restStage, treeBase]
    have htape := tape_eq W P _ v v' he ht
    have hs := hr (qSalt T u) (by
      change 6 < treeBase T + 6
      simp [treeBase]; split <;> (try split) <;> omega)
    have hl := P.leaf_local w (tapeR W.toWire P.toProver v') (trOf v) (trOf v') T u
      (fun j _ hj => he (.inl j) hj)
    simp only [gram, htape, hl, hs, R1PhaseProver.toProver]
  · have hj (j : Fin 2) := hr (childQ T n j) (PhaseScheduleBin.child_before_parent T n j)
    simp only [gram, nodeBytes, hj]

/-- Every phase-refined instance is causal at every answer vector. The only
assumptions are the explicit message/leaf dependency contracts; chronology
and commitment bytes are constructed by toProver. -/
theorem phase_causal (w : h.Instance) : RCausal W.toWire P.toProver h B outputs x w := by
  apply (causal_iff W.toWire P.toProver h B outputs x w).mpr
  intro sec d p v v' he
  have hs : StageAgree W P p v v' := fun q hq => he q (stage_before q p hq)
  cases p with
  | inl j => exact transcript_causal W P w sec d j v v' hs
  | inr c => exact commitment_causal W P w sec d c v v' hs

/-- The exact D80 endpoint premise for the constructed prover, without an
execution-order hypothesis. Identifying the shipped encoding with W/P is
a separate, currently unconstructed source certificate. -/
theorem R_causal_D80 (w : h.Instance) (sec : SecP) (d : OracleAnswer)
    (p : Pos1 P.data.E₁ P.data.E₂) (v v' : Vectors W P)
    (he : Earlier W.toWire P.toProver p v v') :
    attAddr W.toWire P.toProver h B outputs x w sec d v p =
      attAddr W.toWire P.toProver h B outputs x w sec d v' p :=
  (causal_iff W.toWire P.toProver h B outputs x w).mp (phase_causal W P w) sec d p v v' he

#print axioms commitment_causal
#print axioms phase_causal
#print axioms R_causal_D80
end R1Z.PhaseCausalityBin
