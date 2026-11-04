import R1Z.ProverCommitQuotientCoupling

set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitQuotientModel
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.EventsR1PBin R1Z.AgreeR1PBin R1Z.ModelsVR1
  R1Z.FinalR1PBin R1Z.ProverCommitTapeCompletion R1Z.ProverCommitQuotientCoupling
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
/-- The real coupling of the phase-indexed games. -/
def cpQ (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (hc : RCausal W Pr h B outputs x w) (cF : ℕ)
    (hfib : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        quotientDecode (fun e => Pr.tapeOf e.1 e.2) e = some τ)).card = cF) :
    Coupling (fsR1P (F := F) W Pr N hN P Vp).RealRand
      ((Fin (abR1P W N hN).N → (abR1P W N hN).Coins) × (Fin (abR1P W N hN).N → Tape K F)) where
  S := Fin N → AttS (F := F) W Pr
  finS := inferInstance
  nonemptyS := inferInstance
  toR := toRP W Pr R h B outputs x w hN
  toM := toMQ W Pr eCm
  meanR := meanR_P W Pr R h B outputs x w N hN hc
  meanM := meanM_Q W Pr eCm cF hfib N

variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
/-- The real model: every field of `R1RealModelV` for the phase-indexed games. -/
theorem realModel_quotient
    (hin : ∀ w : h.Instance, RAddrIn W Pr R h B outputs x w)
    (hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w)
    (hb : RCommitBytes W Pr) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x)
    (hV : ∀ (w : h.Instance) ch, Vp h ch w ↔ V ch w) (cF : ℕ)
    (hfib : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        quotientDecode (fun e => Pr.tapeOf e.1 e.2) e = some τ)).card = cF)
    (hE₁ : Pr.E₁ ≤ 2 ^ 64) (hE₂ : Pr.E₂ ≤ 2 ^ 64) (L₁ L₂ : ℕ) (hex : RExh Pr L₁ L₂)
    (h₁ : 16 * L₁ ≤ Pr.E₁ * 8) (h₂ : 16 * L₂ ≤ Pr.E₂ * 8) :
    R1RealModelV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) x (N * n1 W Pr) W.qmax
      (2 ^ 255) (εexhP N L₁ L₂ (N * n1 W Pr)) := by
  intro adv w _
  refine ⟨cpQ W Pr R eCm N hN P Vp h B outputs x w (hc w) cF hfib,
    fun j s => chargedQ W Pr eCm N P h V w s (posE W Pr N j), fun _ => True,
    fun j s => addrQ W Pr R N hN h B outputs x w s (posE W Pr N j),
    fun i s => qryQ W Pr eCm N hN P h V B outputs x w adv i s,
    exhQ W Pr R N hN h B outputs x w, ?_, ?_, ?_, mass_exhQ W Pr R N hN h B outputs x hb w L₁ L₂ hex h₁ h₂⟩
  · intro s hH hCE
    change realTest h B outputs (fsR1P W Pr N hN P Vp) adv x w (toRP W Pr R h B outputs x w hN s) =
      middleRealAbortV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) adv x w (toMQ W Pr eCm s)
    rw [middle_completion]
    refine agreeP W Pr R eCm N hN P Vp h V B outputs x w adv (hin w) (hc w) hcom (hV w) s ?_ ?_ ?_ ?_
    · intro p i hch heq
      apply hH
      refine ⟨(posE W Pr N).symm p, i, ?_, ?_⟩
      · show chargedQ W Pr eCm N P h V w s (posE W Pr N ((posE W Pr N).symm p))
        rw [Equiv.apply_symm_apply]
        exact hch
      · show qryQ W Pr eCm N hN P h V B outputs x w adv i s =
          addrQ W Pr R N hN h B outputs x w s (posE W Pr N ((posE W Pr N).symm p))
        rw [Equiv.apply_symm_apply]
        exact heq
    · intro p p' hne heq
      apply hCE
      left
      rcases lt_trichotomy ((posE W Pr N).symm p) ((posE W Pr N).symm p') with hl | he | hg
      · refine ⟨_, _, hl, Or.inl trivial, ?_⟩
        show addrQ W Pr R N hN h B outputs x w s (posE W Pr N ((posE W Pr N).symm p)) =
          addrQ W Pr R N hN h B outputs x w s (posE W Pr N ((posE W Pr N).symm p'))
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact heq
      · exact absurd ((posE W Pr N).symm.injective he) hne
      · refine ⟨_, _, hg, Or.inl trivial, ?_⟩
        show addrQ W Pr R N hN h B outputs x w s (posE W Pr N ((posE W Pr N).symm p')) =
          addrQ W Pr R N hN h B outputs x w s (posE W Pr N ((posE W Pr N).symm p))
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact heq.symm
    · intro k hk
      exact hCE (Or.inr (Or.inl ⟨k, hk⟩))
    · intro p hp
      exact hCE (Or.inr (Or.inr ⟨p, hp⟩))
  · intro j i
    rcases hp : posE W Pr N j with ⟨k, jj | c⟩
    · simp only [hp]
      exact hit_tr W Pr R eCm N hN P h V B outputs x w adv k jj i
    · simp only [hp]
      exact hit_cm W Pr R eCm N hN P h V B outputs x w adv hb hop hcom k c i
  · intro j j' hlt _
    exact pair_all W Pr R N hN h B outputs x w hb hE₁ hE₂ (posE W Pr N j) (posE W Pr N j')
      (fun e => ne_of_lt hlt ((posE W Pr N).injective e))

#print axioms cpQ
#print axioms realModel_quotient
end R1Z.ProverCommitQuotientModel
