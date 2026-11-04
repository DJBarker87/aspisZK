import R1Z.AgreeR1P2Bin
import R1Z.CommitReadsR1

-- Binary-format copy of `R1Z.FinalR1P` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! The real model of the phase-indexed games (DESIGN-R1-REAL §5–§6):
`R1RealModelV` for `fsR1P` / `abR1P` with `M = N · |Pos1|` positions,
`q = qmax`, `Umin = 2^255`, and the exhaustion slot

  εexh = N·16(L₁+L₂)/2^496 + N·|Pos1|/2^255

(mask-sampler exhaustion from the Rust word sampler `CommitReadsR1`, plus a
prover read hitting the frozen digest address).

Named premises added here:
* `wordsE`: the little-endian u32 word stream of expander blocks (8 words per
  32-byte block, word `j` = bytes `4j … 4j+3` little-endian;
  `finFunctionFinEquiv` digit order), and `RExh` (R-commit: the Rust decode
  reports `MaskSampleExhausted` only when one of the two 16-try word streams
  is exhausted). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.FinalR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.LayoutR1PBin R1Z.EventsR1PBin R1Z.AgreeR1PBin R1Z.ModelsVR1
attribute [local instance] Classical.propDecidable

/-! ### Little-endian words of expander blocks -/

abbrev Word := R1Z.CommitReadsR1.Word

/-- One 32-byte block as eight little-endian u32 words. -/
def blockW : OracleAnswer ≃ (Fin 8 → Word) :=
  ((Equiv.arrowCongr (Equiv.refl (Fin 32)) uint8Equiv).trans
    (Equiv.arrowCongr (finProdFinEquiv.trans (finCongr (by norm_num : 8 * 4 = 32))).symm
      (Equiv.refl (Fin UInt8.size)))).trans
  ((Equiv.curry (Fin 8) (Fin 4) (Fin UInt8.size)).trans
    (Equiv.arrowCongr (Equiv.refl (Fin 8))
      (finFunctionFinEquiv.trans (finCongr (by decide : UInt8.size ^ 4 = 2 ^ 32)))))

/-- The word stream of `E` blocks: word `8c + j` is word `j` of block `c`. -/
def wordsE (E : ℕ) : (Fin E → OracleAnswer) ≃ (Fin (E * 8) → Word) :=
  (Equiv.arrowCongr (Equiv.refl (Fin E)) blockW).trans
    ((Equiv.curry (Fin E) (Fin 8) Word).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Word)))

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- R-commit: exhaustion of the Rust mask decode is exhaustion of one of the two
16-try M31 word streams (SeedExpander: `L₁` limbs; Profile21 D expander: `L₂`). -/
def RExh {W : R1Wire K CommitHandle Aux} (Pr : R1ProverP K CommitHandle Aux F W) (L₁ L₂ : ℕ) : Prop :=
  ∀ e₁ e₂, Pr.tapeOf e₁ e₂ = none →
    R1Z.CommitReadsR1.Exhausted (wordsE Pr.E₁ e₁) L₁ ∨ R1Z.CommitReadsR1.Exhausted (wordsE Pr.E₂ e₂) L₂

section Model
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
  (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
  (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)

/-- The exhaustion slot: a mask stream is exhausted, or a prover read hits the
frozen digest address. -/
def exhQ (w : h.Instance) (s : Fin N → AttS (F := F) W Pr) : Prop :=
  (∃ k, Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1) = none) ∨
    (∃ p, addrQ W Pr R N hN h B outputs x w s p = W.pubBytes x)

def εexhP (L₁ L₂ M : ℕ) : ℚ := (N : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 + (M : ℚ) * (1 / 2 ^ 255)

theorem mp_proj :
    MP (fun a : AttS (F := F) W Pr => (eV W Pr a.2.1).2.2.1) := by
  have h1 : MP (fun a : AttS (F := F) W Pr => a.2) := mp_snd
  have h2 : MP (fun r : (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) × (Tape K F × W.Tab) => r.1) := mp_fst
  have h3 := mp_equiv (eV W Pr)
  have h4 : MP (fun q : (TRead → OracleAnswer) × (Fin 3 → OracleAnswer) ×
      (((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) × (RIdx → OracleAnswer)) => q.2) := mp_snd
  have h5 : MP (fun q : (Fin 3 → OracleAnswer) ×
      (((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) × (RIdx → OracleAnswer)) => q.2) := mp_snd
  have h6 : MP (fun q : ((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) × (RIdx → OracleAnswer) =>
      q.1) := mp_fst
  exact mp_comp (mp_comp (mp_comp (mp_comp (mp_comp h1 h2) h3) h4) h5) h6

/-- The word space of the two streams of all attempts and its block form. -/
def eWords : (Fin N → (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) ≃
    (Fin N → (Fin (Pr.E₁ * 8) → Word) × (Fin (Pr.E₂ * 8) → Word)) :=
  Equiv.arrowCongr (Equiv.refl (Fin N)) (Equiv.prodCongr (wordsE Pr.E₁) (wordsE Pr.E₂))

theorem mass_exhaust (L₁ L₂ : ℕ) (hex : RExh Pr L₁ L₂) (h₁ : 16 * L₁ ≤ Pr.E₁ * 8) (h₂ : 16 * L₂ ≤ Pr.E₂ * 8) :
    mass (fun s : Fin N → AttS (F := F) W Pr => ∃ k, Pr.tapeOf (e₁Of (s k).2.1) (e₂Of (s k).2.1) = none) ≤
      (N : ℚ) * (16 * (L₁ + L₂)) / 2 ^ 496 := by
  let Gb : (Fin N → (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) → Prop := fun e =>
    ∃ k, R1Z.CommitReadsR1.Exhausted (wordsE Pr.E₁ (e k).1) L₁ ∨
      R1Z.CommitReadsR1.Exhausted (wordsE Pr.E₂ (e k).2) L₂
  have hm : mass (fun s : Fin N → AttS (F := F) W Pr => Gb (fun k => (eV W Pr (s k).2.1).2.2.1)) = mass Gb := by
    unfold mass
    exact mp_pi (mp_proj W Pr) N (fun e => @ite ℚ (Gb e) (Classical.propDecidable _) 1 0)
  have hw : mass Gb = mass (fun ws : Fin N → (Fin (Pr.E₁ * 8) → Word) × (Fin (Pr.E₂ * 8) → Word) =>
      ∃ k, R1Z.CommitReadsR1.Exhausted (ws k).1 L₁ ∨ R1Z.CommitReadsR1.Exhausted (ws k).2 L₂) := by
    rw [mass_equiv (eWords W Pr N) Gb]
    refine mass_congr _ _ (fun ws => ?_)
    simp [Gb, eWords]
  refine (mass_mono _ (fun s : Fin N → AttS (F := F) W Pr => Gb (fun k => (eV W Pr (s k).2.1).2.2.1))
    (fun s hs => ?_)).trans ?_
  · obtain ⟨k, hk⟩ := hs
    exact ⟨k, hex _ _ hk⟩
  · rw [hm, hw]
    exact R1Z.CommitReadsR1.mass_exh_attempts N L₁ L₂ _ _ h₁ h₂

theorem pf_pub (hb : RCommitBytes W Pr) (w : h.Instance) (p : Fin N × Pos1 Pr.E₁ Pr.E₂) :
    PairFresh (fun _ : Fin N → AttS (F := F) W Pr => W.pubBytes x)
      (fun s => addrQ W Pr R N hN h B outputs x w s p) (2 ^ 255) := by
  obtain ⟨k, j | c⟩ := p
  · exact pairFresh_of_lens ((frameP W Pr h B outputs x w N).lens k (fc j)) _
      (taddr (frameP W Pr h B outputs x w N) k j) (extract j) _ umin_le_card_ans (fun _ _ => rfl)
      (taddr_extract (frameP W Pr h B outputs x w N) k j)
  · exact cm_pf W Pr R N hN h B outputs x w hb k c _ (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

theorem card_posP : Fintype.card (Fin N × Pos1 Pr.E₁ Pr.E₂) = N * n1 W Pr := by
  rw [Fintype.card_prod, Fintype.card_fin]

theorem mass_exhQ (hb : RCommitBytes W Pr) (w : h.Instance) (L₁ L₂ : ℕ) (hex : RExh Pr L₁ L₂)
    (h₁ : 16 * L₁ ≤ Pr.E₁ * 8) (h₂ : 16 * L₂ ≤ Pr.E₂ * 8) :
    mass (exhQ W Pr R N hN h B outputs x w) ≤ εexhP N L₁ L₂ (N * n1 W Pr) := by
  refine (mass_or_le _ _).trans (add_le_add (mass_exhaust W Pr N L₁ L₂ hex h₁ h₂) ?_)
  have hu := mass_exists_le_card
    (fun (p : Fin N × Pos1 Pr.E₁ Pr.E₂) (s : Fin N → AttS (F := F) W Pr) =>
      addrQ W Pr R N hN h B outputs x w s p = W.pubBytes x)
    (1 / ((2 ^ 255 : ℕ) : ℚ)) (fun p => by
      have := pairFresh_mass (fun s => addrQ W Pr R N hN h B outputs x w s p)
        (fun _ => W.pubBytes x) (2 ^ 255) (by positivity) (Or.inr (pf_pub W Pr R N hN h B outputs x hb w p))
      exact this)
  rw [card_posP W Pr N] at hu
  push_cast at hu ⊢
  exact hu

/-- The real model: every field of `R1RealModelV` for the phase-indexed games. -/
theorem realModel_R1P
    (hin : ∀ w : h.Instance, RAddrIn W Pr R h B outputs x w)
    (hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w)
    (hb : RCommitBytes W Pr) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x)
    (hV : ∀ (w : h.Instance) ch, Vp h ch w ↔ V ch w) (cF : ℕ)
    (hfib : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF)
    (hE₁ : Pr.E₁ ≤ 2 ^ 64) (hE₂ : Pr.E₂ ≤ 2 ^ 64) (L₁ L₂ : ℕ) (hex : RExh Pr L₁ L₂)
    (h₁ : 16 * L₁ ≤ Pr.E₁ * 8) (h₂ : 16 * L₂ ≤ Pr.E₂ * 8) :
    R1RealModelV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) x (N * n1 W Pr) W.qmax
      (2 ^ 255) (εexhP N L₁ L₂ (N * n1 W Pr)) := by
  intro adv w _
  refine ⟨cpP W Pr R eCm N hN P Vp h B outputs x w (hc w) cF hfib,
    fun j s => chargedQ W Pr eCm N P h V w s (posE W Pr N j), fun _ => True,
    fun j s => addrQ W Pr R N hN h B outputs x w s (posE W Pr N j),
    fun i s => qryQ W Pr eCm N hN P h V B outputs x w adv i s,
    exhQ W Pr R N hN h B outputs x w, ?_, ?_, ?_, mass_exhQ W Pr R N hN h B outputs x hb w L₁ L₂ hex h₁ h₂⟩
  · intro s hH hCE
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

end Model

#print axioms blockW
#print axioms wordsE
#print axioms mp_proj
#print axioms eWords
#print axioms mass_exhaust
#print axioms pf_pub
#print axioms card_posP
#print axioms mass_exhQ
#print axioms realModel_R1P
end R1Z.FinalR1PBin
