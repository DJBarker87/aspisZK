import R0Z.HvzkV

/-! ZF2 (zf1/DESIGN-ZF2-SIMULATOR.txt §5.2): the J0c abort composition with
the simulator as a parameter.

`HvzkV` fixes the ideal side to the choice simulator `simV`.  Here the
simulator is any function `sim : Challenges K → Tape K F → View`; its law is
compared with the honest view on `P ∧ V` (`HVZK_onS`), and ZK_FS is stated for
`fs.ideal sim` (`ZK_FSS`).  The real side (`middleRealAbortV`,
`RealAbortCouplingV`, `poleBad`, `attemptBad`) does not mention the simulator
and is reused from `HvzkV` unchanged.  The proofs are those of `HvzkV`
(`real_hybrid_eq`, `hybrid_ideal_le`, `abortReductionV_of_couplings`) with
`simV …` replaced by `sim`. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.HvzkS
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort R0Z.HvzkV
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [HonestView.BatchedLayer K Bat]

/-- Perfect HVZK on `P` for the instances valid at each challenge, against a
given simulator. -/
def HVZK_onS (P : Challenges K → Prop) (h : HonestProver K) (V : Challenges K → h.Instance → Prop)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat) : Prop :=
  ∀ (w : h.Instance) (ch : Challenges K), P ch → V ch w → h.public w = x.1 →
    EqualLaws (view (Bat := Bat) h B outputs x w ch) (sim ch)

/-- Hybrid: the honest acceptance rule, the given simulator. -/
def hybridAbortS (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat) (w : h.Instance) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w)
    (fun coin t => sim (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

/-- The simulator's retrying game: acceptance on the public `P` only. -/
def middleIdealAbortS (P : Challenges K → Prop)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin))
    (fun coin t => sim (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

/-- The ideal test with the given simulator. -/
def idealTestS (fs : FSExperiments K CommitHandle Aux Bat F) (adv : fs.Adversary)
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat) : fs.IdealRand → ℚ :=
  fun r => bit (fs.observe adv (fs.ideal sim adv x r))

/-- ZK_FS with the given simulator. -/
def ZK_FSS (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat) (ε : ℚ) : Prop :=
  ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) - mean (idealTestS fs adv x sim)| ≤ ε

section Games
variable (P : Challenges K → Prop) (h : HonestProver K) (V : Challenges K → h.Instance → Prop)
  (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
  (fs : FSExperiments K CommitHandle Aux Bat F)
  (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
  (x : Statement K CommitHandle)
  (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat)

theorem real_hybrid_eqS (w : h.Instance) (hw : h.public w = x.1)
    (hh : HVZK_onS P h V B outputs x sim) :
    mean (middleRealAbortV P h V B outputs fs ab adv x w) =
      mean (hybridAbortS P h V fs ab adv x sim w) := by
  haveI : Nonempty (Tape K F) := ⟨(0, 0)⟩
  exact retry_means_eq ab.N _ _ _ _ _
    (fun coin hc => hh w (ab.draw adv x coin) hc.1 hc.2 hw)

theorem hybrid_ideal_leS (w : h.Instance) :
    |mean (hybridAbortS P h V fs ab adv x sim w) -
      mean (middleIdealAbortS P fs ab adv x sim)| ≤
      eventMass (fun ct : (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) =>
        poleBad P h V ab adv x w ct.1) := by
  have hbit : ∀ c k v, 0 ≤ bit (fs.observe adv (ab.extend adv x c k v)) ∧
      bit (fs.observe adv (ab.extend adv x c k v)) ≤ 1 :=
    fun _ _ _ => ⟨bit_nonneg _, bit_le_one _⟩
  have hfail : ∀ c, 0 ≤ bit (fs.observe adv (ab.fail adv x c)) ∧
      bit (fs.observe adv (ab.fail adv x c)) ≤ 1 :=
    fun _ => ⟨bit_nonneg _, bit_le_one _⟩
  refine until_bad _ _ (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _)
    (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _) _ ?_
  intro ct hnb
  have hiff : ∀ k, (P (ab.draw adv x (ct.1 k)) ∧ V (ab.draw adv x (ct.1 k)) w) ↔
      P (ab.draw adv x (ct.1 k)) := by
    intro k
    refine ⟨fun hk => hk.1, fun hk => ⟨hk, ?_⟩⟩
    by_contra hv
    exact hnb ⟨k, hk, hv⟩
  have hfg := firstGood_congr (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w)
    (fun coin => P (ab.draw adv x coin)) ct.1 hiff
  simp only [hybridAbortS, middleIdealAbortS, retryTest, hfg]

end Games

/-- The ideal coupling for the given simulator (`IdealAbortCouplingV` with
`simV` replaced by `sim`). -/
def IdealAbortCouplingS (P : Challenges K → Prop)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat) (ε_prog : ℚ) : Prop :=
  ∀ (adv : fs.Adversary),
    ∃ (cp : Coupling fs.IdealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (Prog : cp.S → Prop),
      (∀ s, ¬ Prog s →
        middleIdealAbortS P fs ab adv x sim (cp.toM s) = idealTestS fs adv x sim (cp.toR s)) ∧
      eventMass Prog ≤ ε_prog

/-- Theorem B with the pole term, for a given simulator:
error `ε_hit + ε_coll + ε_prog + N·q`. -/
theorem zkfs_of_hvzk_onS_terms (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle)
    (sim : Challenges K → Tape K F → View K CommitHandle Aux Bat)
    (hh : HVZK_onS P h V B outputs x sim)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_hit ε_coll ε_prog q : ℚ)
    (hreal : RealAbortCouplingV P h V B outputs fs ab x ε_hit ε_coll)
    (hideal : IdealAbortCouplingS P fs ab x sim ε_prog)
    (hq : ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
      eventMass (attemptBad P h V ab adv x w) ≤ q) :
    ZK_FSS h B outputs fs x sim (ε_hit + ε_coll + ε_prog + ab.N * q) := by
  intro adv w hw
  have hbit : ∀ c k v, 0 ≤ bit (fs.observe adv (ab.extend adv x c k v)) ∧
      bit (fs.observe adv (ab.extend adv x c k v)) ≤ 1 :=
    fun _ _ _ => ⟨bit_nonneg _, bit_le_one _⟩
  have hfail : ∀ c, 0 ≤ bit (fs.observe adv (ab.fail adv x c)) ∧
      bit (fs.observe adv (ab.fail adv x c)) ≤ 1 :=
    fun _ => ⟨bit_nonneg _, bit_le_one _⟩
  -- real side
  have hR : |mean (realTest h B outputs fs adv x w) -
      mean (middleRealAbortV P h V B outputs fs ab adv x w)| ≤ ε_hit + ε_coll := by
    obtain ⟨cp, Hit, Coll, hag, hH, hC⟩ := hreal adv w hw
    rw [← cp.meanR (realTest h B outputs fs adv x w),
      ← cp.meanM (middleRealAbortV P h V B outputs fs ab adv x w)]
    have hb := until_bad (fun s => realTest h B outputs fs adv x w (cp.toR s))
      (fun s => middleRealAbortV P h V B outputs fs ab adv x w (cp.toM s))
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
      (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _)
      (fun s => Hit s ∨ Coll s)
      (fun s hs => hag s (fun hh => hs (Or.inl hh)) (fun hh => hs (Or.inr hh)))
    have ho := eventMass_or_le Hit Coll
    linarith
  -- ideal side
  have hI : |mean (middleIdealAbortS P fs ab adv x sim) - mean (idealTestS fs adv x sim)| ≤ ε_prog := by
    obtain ⟨cp, Prog, hag, hP⟩ := hideal adv
    rw [← cp.meanR (idealTestS fs adv x sim), ← cp.meanM (middleIdealAbortS P fs ab adv x sim)]
    have hb := until_bad (fun s => middleIdealAbortS P fs ab adv x sim (cp.toM s))
      (fun s => idealTestS fs adv x sim (cp.toR s))
      (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
      Prog hag
    linarith
  have hmid := real_hybrid_eqS P h V B outputs fs ab adv x sim w hw hh
  have hbad := (hybrid_ideal_leS P h V fs ab adv x sim w).trans
    (poleBad_mass_le P h V fs ab adv x w q (hq adv w hw))
  rw [hmid] at hR
  have t1 := abs_sub_le (mean (realTest h B outputs fs adv x w))
    (mean (hybridAbortS P h V fs ab adv x sim w))
    (mean (middleIdealAbortS P fs ab adv x sim))
  have t2 := abs_sub_le (mean (realTest h B outputs fs adv x w))
    (mean (middleIdealAbortS P fs ab adv x sim))
    (mean (idealTestS fs adv x sim))
  linarith

#print axioms HVZK_onS
#print axioms hybridAbortS
#print axioms middleIdealAbortS
#print axioms idealTestS
#print axioms ZK_FSS
#print axioms real_hybrid_eqS
#print axioms hybrid_ideal_leS
#print axioms IdealAbortCouplingS
#print axioms zkfs_of_hvzk_onS_terms
end R0Z.HvzkS
