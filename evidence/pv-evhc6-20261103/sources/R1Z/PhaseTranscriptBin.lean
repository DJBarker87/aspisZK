import R1Z.PhaseLocalityBin

set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseTranscriptBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched R1Z.GamesR1
  R1Z.GamesR1PBin R1Z.LayoutR1PBin R1Z.TranscriptR1 R1Z.PhaseScheduleBin
  R1Z.PhaseLocalityBin

def CoordBefore (c : Coord) (cut : ℕ) : Prop :=
  match c with
  | .root => 25 < cut
  | .sel => ∀ k : Fin 8, transcriptStage (.qa k) < cut
  | .ans j => transcriptStage j < cut

theorem chain_before (j : TRead) : CoordBefore (fc j) (transcriptStage j) := by
  cases j with
  | init => simp [fc, CoordBefore, transcriptStage]
  | absS i =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => simp [fc, CoordBefore, transcriptStage]
    | succ i => simp [fc, CoordBefore, transcriptStage]; split <;> split <;> omega
  | sqS i => simp [fc, CoordBefore, transcriptStage]; split <;> omega
  | advS i => simp [fc, CoordBefore, transcriptStage]; split <;> omega
  | reseed => simp [fc, CoordBefore, transcriptStage]
  | absO i =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => simp [fc, CoordBefore, transcriptStage]
    | succ i => simp [fc, CoordBefore, transcriptStage]; split <;> split <;> omega
  | sqO i => simp [fc, CoordBefore, transcriptStage]; split <;> omega
  | advO i => simp [fc, CoordBefore, transcriptStage]; split <;> omega
  | absQ => simp [fc, CoordBefore, transcriptStage]
  | qb k =>
    rcases k with ⟨k, hk⟩
    cases k <;> simp [fc, CoordBefore, transcriptStage] <;> omega
  | qa k =>
    rcases k with ⟨k, hk⟩
    cases k <;> simp [fc, CoordBefore, transcriptStage] <;> omega
  | absR => simp [fc, CoordBefore, transcriptStage]; intro k; have := k.isLt; omega
  | sqR => simp [fc, CoordBefore, transcriptStage]
  | advR => simp [fc, CoordBefore, transcriptStage]

theorem transcript_after_tape (j : TRead) : 5 < transcriptStage j := by
  cases j <;> simp only [transcriptStage] <;> (try split) <;> omega

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {h : HonestProver K} {B : PackBasis F}
  {outputs : Statement K CommitHandle → Challenges K → Aux}
  {x : Statement K CommitHandle} (W : R1PhaseWire h B outputs x)
  (P : R1PhaseProver h B outputs x W)

abbrev Vectors := Pos1 P.data.E₁ P.data.E₂ → OracleAnswer

def StageAgree (p : Pos1 P.data.E₁ P.data.E₂) (v v' : Vectors W P) : Prop :=
  ∀ q, stage q < stage p → v q = v' q

theorem tape_eq (p : Pos1 P.data.E₁ P.data.E₂) (v v' : Vectors W P)
    (he : StageAgree W P p v v') (hp : 5 < stage p) :
    tapeR W.toWire P.toProver v = tapeR W.toWire P.toProver v' := by
  have h₁ : e₁Of v = e₁Of v' := funext (fun c => he _ hp)
  have h₂ : e₂Of v = e₂Of v' := funext (fun c => he _ hp)
  simp only [tapeR, R1PhaseProver.toProver, h₁, h₂]

theorem transcript_causal (w : h.Instance) (sec : SecP) (d : OracleAnswer)
    (j : TRead) (v v' : Vectors W P) (he : StageAgree W P (.inl j) v v') :
    attAddr W.toWire P.toProver h B outputs x w sec d v (.inl j) =
      attAddr W.toWire P.toProver h B outputs x w sec d v' (.inl j) := by
  have ht := tape_eq W P (.inl j) v v' he (transcript_after_tape j)
  have hs : SqAgree (transcriptStage j) (trOf v) (trOf v') :=
    fun q _ hq => he (.inl q) hq
  have hc : fieldVal (fc j) (recP W.toWire x
      (view h B outputs x w (chOf W.toWire (trOf v)) (tapeR W.toWire P.toProver v))
      (trOf v) (rootsOf v)) =
      fieldVal (fc j) (recP W.toWire x
      (view h B outputs x w (chOf W.toWire (trOf v')) (tapeR W.toWire P.toProver v'))
      (trOf v') (rootsOf v')) := by
    have hb := chain_before j
    cases hf : fc j with
    | root => exact he (.inr (.inl 0)) (by simpa [hf, CoordBefore, stage, treeBase] using hb)
    | ans q => exact he (.inl q) (by simpa only [hf, CoordBefore, stage] using hb)
    | sel =>
      have hb : ∀ k : Fin 8, transcriptStage (.qa k) < transcriptStage j := by
        simpa [hf, CoordBefore] using hb
      have hq : (fun k => trOf v (.qb k)) = (fun k => trOf v' (.qb k)) := by
        funext k
        apply he (.inl (.qb k))
        have hk := k.isLt
        change 160 + 2 * k.val < transcriptStage j
        have hb' : 161 + 2 * k.val < transcriptStage j := by
          simpa [hf, CoordBefore, transcriptStage] using hb k
        omega
      change trOf v (.qa (W.toWire.kstarOf (fun k => trOf v (.qb k)))) =
        trOf v' (.qa (W.toWire.kstarOf (fun k => trOf v' (.qb k))))
      rw [hq]
      apply he (.inl _)
      simpa only [hf, CoordBefore, stage] using hb (W.toWire.kstarOf (fun k => trOf v' (.qb k)))
  change addrWith j _ _ = addrWith j _ _
  rw [hc]
  cases j with
  | absS i =>
    have hm := W.frame_local w (tapeR W.toWire P.toProver v') (trOf v) (trOf v')
      (rootsOf v 1) (rootsOf v' 1) i hs (by
        intro hi; apply he (.inr (.inl 1)); simp [stage, treeBase, transcriptStage, hi])
    simpa only [addrWith, recP, ht] using congrArg
      (fun m => R1Z.LensR1.ans (fieldVal (fc (.absS i)) (recP W.toWire x
        (view h B outputs x w (chOf W.toWire (trOf v')) (tapeR W.toWire P.toProver v'))
        (trOf v') (rootsOf v'))) ++ ([0, 0xa0 + i.val.toUInt8] ++ m)) hm
  | absO i =>
    have hm := W.payload_local w (tapeR W.toWire P.toProver v') (trOf v) (trOf v')
      (rootsOf v 2) (rootsOf v' 2) i hs (by
        intro hi; apply he (.inr (.inl 2)); simp [stage, treeBase, transcriptStage, hi])
    simp only [addrWith, recP, ht, hm]
  | absQ =>
    have hm := W.final_local w (tapeR W.toWire P.toProver v') (trOf v) (trOf v') hs
    simp only [addrWith, recP, ht, hm]
  | _ => rfl

#print axioms chain_before
#print axioms transcript_after_tape
#print axioms tape_eq
#print axioms transcript_causal
end R1Z.PhaseTranscriptBin
