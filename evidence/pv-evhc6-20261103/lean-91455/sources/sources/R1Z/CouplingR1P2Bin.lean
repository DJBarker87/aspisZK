import R1Z.CouplingR1PBin

-- Binary-format copy of `R1Z.CouplingR1P2` (LOG D76): the text is unchanged except that it is
-- built over `GamesR1PBin` / `LayoutR1P*Bin` (binary node index and `0x12 ‖ 2 children`).

/-! The real coupling, part 2 (DESIGN-R1-REAL §4): `meanM_P` (the middle
coins and tapes are uniform) and `meanR_P` (the reprogrammed table and the
secrets are uniform), assembled into `cpP : Coupling`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.CouplingR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

instance instPos1Fin {E₁ E₂ : ℕ} : Fintype (Pos1 E₁ E₂) := inferInstance
instance instPos1Deq {E₁ E₂ : ℕ} : DecidableEq (Pos1 E₁ E₂) := inferInstance
instance instPos1Fun {E₁ E₂ : ℕ} : Fintype (Pos1 E₁ E₂ → OracleAnswer) :=
  @Pi.instFintype _ _ instPos1Deq instPos1Fin (fun _ => inferInstance)
instance instAttSFin (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) :
    Fintype (AttS (F := F) W Pr) :=
  inferInstanceAs (Fintype (SecP × (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) × Tape K F × W.Tab))

section Means
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer))

instance : Nonempty (Tape K F) := ⟨(0, 0)⟩

/-- An attempt's answers split by read kind. -/
def eV : (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) ≃ (TRead → OracleAnswer) × (Fin 3 → OracleAnswer) ×
    (((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) × (RIdx → OracleAnswer)) where
  toFun v := (trOf v, rootsOf v, ((e₁Of v, e₂Of v), restOf v))
  invFun q p := match p with
    | .inl j => q.1 j
    | .inr (.inl i) => q.2.1 i
    | .inr (.inr (.inl (.inl c))) => q.2.2.1.1 c
    | .inr (.inr (.inl (.inr c))) => q.2.2.1.2 c
    | .inr (.inr (.inr r)) => q.2.2.2 r
  left_inv v := by
    funext p
    rcases p with j | i | (c | c) | r <;> rfl
  right_inv q := rfl

/-- Regroup: the coin part and the (expander answers, spare tape) part. -/
def rearr {A₁ A₂ E A₄ T B : Type} : ((A₁ × A₂ × (E × A₄)) × (T × B)) ≃ ((A₁ × A₂ × A₄ × B) × (E × T)) where
  toFun p := ((p.1.1, p.1.2.1, p.1.2.2.2, p.2.2), (p.1.2.2.1, p.2.1))
  invFun q := ((q.1.1, q.1.2.1, (q.2.1, q.1.2.2.1)), (q.2.2, q.1.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def eC : ((TRead → OracleAnswer) × (Fin 3 → OracleAnswer) × (RIdx → OracleAnswer) × W.Tab) ≃
    R1Coins W.Cm W.Tab where
  toFun q := (q.1, q.2.1, eCm.symm q.2.2.1, q.2.2.2)
  invFun c := (c.1, c.2.1, eCm c.2.2.1, c.2.2.2)
  left_inv q := by simp
  right_inv c := by simp

theorem mp_gM (cF : ℕ)
    (hfib : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF) :
    MP (gM W Pr eCm) := by
  have hd : MP (fun p : ((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) × Tape K F =>
      (Pr.tapeOf p.1.1 p.1.2).getD p.2) :=
    fun f => R0Z.FsAbortTape.mean_decodeOrSpare
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) => Pr.tapeOf e.1 e.2) cF
      (fun τ => by convert hfib τ) f
  have h1 : MP (fun a : AttS (F := F) W Pr => a.2) := mp_snd
  have h2 : MP (fun p : (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) × (Tape K F × W.Tab) =>
      (eV W Pr p.1, (Equiv.refl (Tape K F × W.Tab)) p.2)) :=
    mp_prodMap (mp_equiv (eV W Pr)) (mp_equiv (Equiv.refl _))
  have h3 := mp_equiv (rearr (A₁ := TRead → OracleAnswer) (A₂ := Fin 3 → OracleAnswer)
    (E := (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) (A₄ := RIdx → OracleAnswer)
    (T := Tape K F) (B := W.Tab))
  have h4 := mp_prodMap (mp_equiv (eC W eCm)) hd
  have hc := mp_comp (mp_comp (mp_comp h1 h2) h3) h4
  intro f
  exact hc f

theorem meanM_P (cF : ℕ)
    (hfib : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF) (N : ℕ)
    (f : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F) → ℚ) :
    mean (fun s : Fin N → AttS (F := F) W Pr => f (toMP W Pr eCm s)) = mean f := by
  have hp := mp_pi (mp_gM W Pr eCm cF hfib) N
  have he := mp_equiv (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => R1Coins W.Cm W.Tab)
    (fun _ => Tape K F))
  exact (mp_comp hp he) f

end Means

section RealMean
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
  (h : HonestProver K) (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
  (x : Statement K CommitHandle) (w : h.Instance) (N : ℕ) (hN : 0 < N)

abbrev QP := (Fin N → SecP) × (Fin (N * n1 W Pr) → OracleAnswer) × W.Tab
abbrev ExP := (Fin N → Tape K F) × ({j : Fin N // j ≠ ⟨0, hN⟩} → W.Tab)

def eS : (Fin N → AttS (F := F) W Pr) ≃ QP W Pr N × ExP (K := K) (F := F) W N hN where
  toFun s := ((fun k => (s k).1, uVec W Pr s, (s ⟨0, hN⟩).2.2.2),
    (fun k => (s k).2.2.1, fun j => (s j.1).2.2.2))
  invFun q k := (q.1.1 k, fun p => q.1.2.1 (finProdFinEquiv (k, Pr.ord.symm p)), q.2.1 k,
    if hk : k = ⟨0, hN⟩ then q.1.2.2 else q.2.2 ⟨k, hk⟩)
  left_inv s := by
    funext k
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
    · funext p
      simp [uVec]
    · show (if hk : k = ⟨0, hN⟩ then (s ⟨0, hN⟩).2.2.2 else (s k).2.2.2) = (s k).2.2.2
      by_cases hk : k = ⟨0, hN⟩
      · subst hk
        simp
      · simp [hk]
  right_inv q := by
    refine Prod.ext (Prod.ext rfl (Prod.ext ?_ ?_)) (Prod.ext rfl ?_)
    · funext g
      show q.1.2.1 (finProdFinEquiv ((finProdFinEquiv.symm g).1,
        Pr.ord.symm (Pr.ord (finProdFinEquiv.symm g).2))) = q.1.2.1 g
      rw [Equiv.symm_apply_apply]
      exact congrArg _ (Equiv.apply_symm_apply _ _)
    · show (if hk : (⟨0, hN⟩ : Fin N) = ⟨0, hN⟩ then q.1.2.2 else q.2.2 ⟨⟨0, hN⟩, hk⟩) = q.1.2.2
      simp
    · funext j
      show (if hk : j.1 = ⟨0, hN⟩ then q.1.2.2 else q.2.2 ⟨j.1, hk⟩) = q.2.2 j
      simp [j.2]

/-- The real side of the coupling as a function of the lazy coordinates. -/
def PhiP (q : QP W Pr N) : W.Tab × (Fin N → SecP) :=
  (R.eTab.symm (progF (Frz R x) (aA W Pr R h B outputs x w q.1) (R.eTab q.2.2) q.2.1), q.1)

theorem mp_PhiP (hc : RCausal W Pr h B outputs x w) : MP (PhiP W Pr R h B outputs x w N) := by
  intro f
  rw [LawTransport.mean_product]
  have inner : ∀ sec : Fin N → SecP,
      mean (fun r : (Fin (N * n1 W Pr) → OracleAnswer) × W.Tab =>
        f (PhiP W Pr R h B outputs x w N (sec, r))) = mean (fun tab : W.Tab => f (tab, sec)) := by
    intro sec
    have hl : MP (fun p : (R.A → OracleAnswer) × (Fin (N * n1 W Pr) → OracleAnswer) =>
        progF (Frz R x) (aA W Pr R h B outputs x w sec) p.1 p.2) :=
      fun F => mean_progF (Frz R x) _ (causalF_aA W Pr R h B outputs x w hc sec) F
    have hs : MP (fun r : (Fin (N * n1 W Pr) → OracleAnswer) × W.Tab => (R.eTab r.2, r.1)) :=
      mp_equiv ((Equiv.prodComm _ _).trans (Equiv.prodCongr R.eTab (Equiv.refl _)))
    have hall := mp_comp (mp_comp hs hl) (mp_equiv R.eTab.symm)
    exact hall (fun tab => f (tab, sec))
  simp only [inner]
  rw [LawTransport.mean_product (f := f), mean_comm]

theorem meanR_P (hc : RCausal W Pr h B outputs x w) (f : W.Tab × (Fin N → SecP) → ℚ) :
    mean (fun s : Fin N → AttS (F := F) W Pr => f (toRP W Pr R h B outputs x w hN s)) = mean f := by
  have h1 := mp_comp (mp_equiv (eS W Pr N hN))
    (mp_fst (X := QP W Pr N) (Y := ExP (K := K) (F := F) W N hN))
  exact (mp_comp h1 (mp_PhiP W Pr R h B outputs x w N hc)) f

end RealMean

/-- The real coupling of the phase-indexed games. -/
def cpP (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W) (R : RomModel W)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (hc : RCausal W Pr h B outputs x w) (cF : ℕ)
    (hfib : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF) :
    Coupling (fsR1P (F := F) W Pr N hN P Vp).RealRand
      ((Fin (abR1P W N hN).N → (abR1P W N hN).Coins) × (Fin (abR1P W N hN).N → Tape K F)) where
  S := Fin N → AttS (F := F) W Pr
  finS := inferInstance
  nonemptyS := inferInstance
  toR := toRP W Pr R h B outputs x w hN
  toM := toMP W Pr eCm
  meanR := meanR_P W Pr R h B outputs x w N hN hc
  meanM := meanM_P W Pr eCm cF hfib N

#print axioms eV
#print axioms mp_gM
#print axioms meanM_P
#print axioms eS
#print axioms mp_PhiP
#print axioms meanR_P
#print axioms cpP
end R1Z.CouplingR1PBin
