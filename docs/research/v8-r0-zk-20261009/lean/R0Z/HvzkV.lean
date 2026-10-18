import R0Z.HonestValid

/-! J0c (LOG D40.3, route (a)): HVZK with a per-challenge valid-instance set,
and the abort composition with a witness-dependent bad event.

* `simV`: the simulator that, at each challenge, runs the honest view of SOME
  instance valid at that challenge (falling back to the plain simulator when
  none exists).  `HVZK_onV P h V` compares it with every instance valid at the
  challenge.
* `MaskImageOnV P h V`: both mask-image clauses on the per-challenge valid
  set; `hvzk_on_of_V` derives `HVZK_onV` from it through `hvzk_on_of` applied
  to the single-challenge restricted prover `h.restrict (V ch)`.
* The retrying honest prover accepts attempt coins with `P ∧ V(·, w)`
  (a pole fails the attempt); the simulator retries on the public `P` only.
  The two loops agree off `poleBad`: some attempt has `P ∧ ¬V(·, w)`
  (identical until bad).  `eventMass_exists_le`: that mass is at most
  `N · q` when one attempt's mass is at most `q`.
* `zkfs_of_hvzk_onV` and `zkfs_of_hvzk_onV_terms`: ZK_FS (with the
  per-challenge simulator) with error `ε_real + ε_ideal + ε_pole`, resp.
  `ε_hit + ε_coll + ε_prog + ε_pole`; the reduction bounds, the couplings and
  the per-attempt bad mass are hypotheses.

Generic in the batched layer and in `V`. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.HvzkV
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort
attribute [local instance] Classical.propDecidable

/-! ### Generic counting -/

theorem mean_sum {R ι : Type} [Fintype R] (s : Finset ι) (f : ι → R → ℚ) :
    mean (fun r => ∑ k ∈ s, f k r) = ∑ k ∈ s, mean (f k) := by
  unfold mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem eventMass_mono {S : Type} [Fintype S] (E E' : S → Prop) (h : ∀ s, E s → E' s) :
    eventMass E ≤ eventMass E' := by
  unfold eventMass
  apply mean_le_mean
  intro s
  by_cases hE : E s
  · rw [if_pos hE, if_pos (h s hE)]
  · rw [if_neg hE]
    split_ifs <;> norm_num

/-- Union bound over the attempts of an independent tuple. -/
theorem eventMass_exists_le {C : Type} [Fintype C] [Nonempty C] {N : Nat} (E : C → Prop) (q : ℚ)
    (hq : eventMass E ≤ q) :
    eventMass (fun c : Fin N → C => ∃ k, E (c k)) ≤ N * q := by
  unfold eventMass at hq ⊢
  refine (mean_le_mean _ (fun c : Fin N → C => ∑ k : Fin N, if E (c k) then (1 : ℚ) else 0)
    (fun c => ?_)).trans ?_
  · split_ifs with h
    · obtain ⟨k, hk⟩ := h
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin N => if E (c j) then (1 : ℚ) else 0)
        (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
      simpa only [if_pos hk] using hle
    · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  rw [mean_sum Finset.univ (fun k (c : Fin N → C) => if E (c k) then (1 : ℚ) else 0)]
  have he : ∀ k : Fin N, mean (fun c : Fin N → C => if E (c k) then (1 : ℚ) else 0) =
      mean (fun c : C => if E c then (1 : ℚ) else 0) :=
    fun k => mean_eval k (fun c : C => if E c then (1 : ℚ) else 0)
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg N)

/-- An event of the first factor has its own mass on a product with a
nonempty second factor. -/
theorem eventMass_fst {C T : Type} [Fintype C] [Fintype T] [Nonempty T] (E : C → Prop) :
    eventMass (fun ct : C × T => E ct.1) = eventMass E := by
  unfold eventMass
  rw [LawTransport.mean_product]
  apply congrArg mean
  funext c
  show mean (fun _ : T => if E c then (1 : ℚ) else 0) = _
  exact mean_const _

/-- `firstGood` depends only on the predicate along the tuple. -/
theorem firstGood_congr {C : Type} (Pd₁ Pd₂ : C → Prop) {N : Nat} (c : Fin N → C)
    (h : ∀ k, Pd₁ (c k) ↔ Pd₂ (c k)) : firstGood Pd₁ c = firstGood Pd₂ c := by
  rcases h1 : firstGood Pd₁ c with _ | k₁ <;> rcases h2 : firstGood Pd₂ c with _ | k₂
  · rfl
  · exact absurd ((h k₂).2 (firstGood_spec Pd₂ c k₂ h2)) (firstGood_none Pd₁ c h1 k₂)
  · exact absurd ((h k₁).1 (firstGood_spec Pd₁ c k₁ h1)) (firstGood_none Pd₂ c h2 k₁)
  · have a := firstGood_least Pd₁ c k₁ h1 k₂ ((h k₂).2 (firstGood_spec Pd₂ c k₂ h2))
    have b := firstGood_least Pd₂ c k₂ h2 k₁ ((h k₁).1 (firstGood_spec Pd₁ c k₁ h1))
    rw [le_antisymm a b]

/-! ### HVZK on a per-challenge valid set -/

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [HonestView.BatchedLayer K Bat]

/-- The per-challenge simulator: the honest view of an instance valid at `ch`. -/
def simV (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hx : InLanguage h x)
    (V : Challenges K → h.Instance → Prop) (ch : Challenges K) :
    Tape K F → View K CommitHandle Aux Bat :=
  if hch : ∃ w, V ch w ∧ h.public w = x.1 then view h B outputs x (Classical.choose hch) ch
  else simulator h B outputs x hx ch

/-- Perfect HVZK on `P` for the instances valid at each challenge. -/
def HVZK_onV (P : Challenges K → Prop) (h : HonestProver K) (V : Challenges K → h.Instance → Prop)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) : Prop :=
  ∀ (hx : InLanguage h x) (w : h.Instance) (ch : Challenges K), P ch → V ch w → h.public w = x.1 →
    EqualLaws (view (Bat := Bat) h B outputs x w ch) (simV h B outputs x hx V ch)

/-- Both mask-image clauses on the per-challenge valid set. -/
def MaskImageOnV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F) (x : Statement K CommitHandle) : Prop :=
  (∀ ch, P ch → ∀ w n, V ch w → h.public w = x.1 →
    sRem (Bat := Bat) h B x w ch n ∈ LinearMap.range ((D12.A h.transport B ch).comp Partition.inlM)) ∧
  (∀ ch, P ch → ∀ w w', V ch w → V ch w' → h.public w = x.1 → h.public w' = x.1 →
    cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch ∈ LinearMap.range (D12.A h.transport B ch))

theorem maskImageOnV_mono (P : Challenges K → Prop) (h : HonestProver K)
    (V V' : Challenges K → h.Instance → Prop) (B : PackBasis F) (x : Statement K CommitHandle)
    (hVV : ∀ ch w, P ch → V ch w → V' ch w) :
    MaskImageOnV (Bat := Bat) P h V' B x → MaskImageOnV (Bat := Bat) P h V B x :=
  fun hm => ⟨fun ch hP w n hv hw => hm.1 ch hP w n (hVV ch w hP hv) hw,
    fun ch hP w w' hv hv' hw hw' => hm.2 ch hP w w' (hVV ch w hP hv) (hVV ch w' hP hv') hw hw'⟩

/-- At one challenge, the per-challenge clauses are `MaskImageOn` of the
restricted prover `h.restrict (V ch)`. -/
theorem maskImageOn_point (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F) (x : Statement K CommitHandle)
    (hm : MaskImageOnV (Bat := Bat) P h V B x) (ch : Challenges K) (hP : P ch) :
    MaskImageOn (Bat := Bat) (fun c => c = ch) (ZkStatement.HonestProver.restrict h (V ch)) B x :=
  (R0Z.HonestValid.maskImageOn_restrict_iff h (V ch) (fun c => c = ch) B x).2
    ⟨fun c (hc : c = ch) w n hv hw => by subst hc; exact hm.1 c hP w n hv hw,
      fun c (hc : c = ch) w w' hv hv' hw hw' => by subst hc; exact hm.2 c hP w w' hv hv' hw hw'⟩

theorem view_restrict (h : HonestProver K) (V : h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle)
    (w : (ZkStatement.HonestProver.restrict h V).Instance) (ch : Challenges K) :
    view (Bat := Bat) (ZkStatement.HonestProver.restrict h V) B outputs x w ch =
      view h B outputs x w.1 ch := rfl

/-- `MaskImageOnV ⇒ HVZK_onV`. -/
theorem hvzk_on_of_V [Fintype Bat] (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle) :
    MaskImageOnV (Bat := Bat) P h V B x → HVZK_onV (Bat := Bat) P h V B outputs x := by
  intro hm hx w ch hP hV hw
  have hch : ∃ w, V ch w ∧ h.public w = x.1 := ⟨w, hV, hw⟩
  have hH := hvzk_on_of (Bat := Bat) (fun c => c = ch) (ZkStatement.HonestProver.restrict h (V ch))
    B outputs x (maskImageOn_point P h V B x hm ch hP)
  have hw' := Classical.choose_spec hch
  have hx' : InLanguage (ZkStatement.HonestProver.restrict h (V ch)) x := ⟨⟨w, hV⟩, hw⟩
  have e1 := hH hx' ⟨w, hV⟩ ch rfl hw
  have e2 := hH hx' ⟨Classical.choose hch, hw'.1⟩ ch rfl hw'.2
  rw [view_restrict] at e1 e2
  unfold simV
  rw [dif_pos hch]
  intro v
  exact (e1 v).trans (e2 v).symm

/-! ### The retrying games with a witness-dependent failure -/

/-- The honest retrying prover: an attempt is accepted when `P` holds and the
instance is valid at the drawn challenge. -/
def middleRealAbortV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (w : h.Instance) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w)
    (fun coin t => view h B outputs x w (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

/-- Hybrid: the honest acceptance rule, the per-challenge simulator. -/
def hybridAbortV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) (w : h.Instance) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin) ∧ V (ab.draw adv x coin) w)
    (fun coin t => simV h B outputs x hx V (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

/-- The simulator's retrying game: acceptance on the public `P` only. -/
def middleIdealAbortV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin))
    (fun coin t => simV h B outputs x hx V (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

/-- The witness-dependent bad event: some attempt has `P` but not validity. -/
def poleBad (P : Challenges K → Prop) (h : HonestProver K) (V : Challenges K → h.Instance → Prop)
    {Adv : Type} (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv)
    (x : Statement K CommitHandle) (w : h.Instance) (c : Fin ab.N → ab.Coins) : Prop :=
  ∃ k, P (ab.draw adv x (c k)) ∧ ¬ V (ab.draw adv x (c k)) w

/-- One attempt's bad event. -/
def attemptBad (P : Challenges K → Prop) (h : HonestProver K) (V : Challenges K → h.Instance → Prop)
    {Adv : Type} (ab : AbortBridge K CommitHandle Aux Bat Adv) (adv : Adv)
    (x : Statement K CommitHandle) (w : h.Instance) (coin : ab.Coins) : Prop :=
  P (ab.draw adv x coin) ∧ ¬ V (ab.draw adv x coin) w

/-- The ideal test with the per-challenge simulator. -/
def idealTestV (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) : fs.IdealRand → ℚ :=
  fun r => bit (fs.observe adv (fs.ideal (simV h B outputs x hx V) adv x r))

/-- ZK_FS with the per-challenge simulator. -/
def ZK_FSV (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (ε : ℚ) : Prop :=
  ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) - mean (idealTestV h V B outputs fs adv x hx)| ≤ ε

section Games
variable (P : Challenges K → Prop) (h : HonestProver K) (V : Challenges K → h.Instance → Prop)
  (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
  (fs : FSExperiments K CommitHandle Aux Bat F)
  (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
  (x : Statement K CommitHandle)

theorem real_hybrid_eq (hx : InLanguage h x) (w : h.Instance) (hw : h.public w = x.1)
    (hh : HVZK_onV (Bat := Bat) P h V B outputs x) :
    mean (middleRealAbortV P h V B outputs fs ab adv x w) =
      mean (hybridAbortV P h V B outputs fs ab adv x hx w) := by
  haveI : Nonempty (Tape K F) := ⟨(0, 0)⟩
  exact retry_means_eq ab.N _ _ _ _ _
    (fun coin hc => hh hx w (ab.draw adv x coin) hc.1 hc.2 hw)

theorem hybrid_ideal_le (hx : InLanguage h x) (w : h.Instance) :
    |mean (hybridAbortV P h V B outputs fs ab adv x hx w) -
      mean (middleIdealAbortV P h V B outputs fs ab adv x hx)| ≤
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
  simp only [hybridAbortV, middleIdealAbortV, retryTest, hfg]

/-- The bad mass over the attempts: at most `N` times one attempt's mass. -/
theorem poleBad_mass_le (w : h.Instance) (q : ℚ)
    (hq : eventMass (attemptBad P h V ab adv x w) ≤ q) :
    eventMass (fun ct : (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) =>
      poleBad P h V ab adv x w ct.1) ≤ ab.N * q := by
  haveI : Nonempty (Tape K F) := ⟨(0, 0)⟩
  rw [eventMass_fst (fun c : Fin ab.N → ab.Coins => poleBad P h V ab adv x w c)]
  exact eventMass_exists_le (attemptBad P h V ab adv x w) q hq

/-- The reduction certificate for the per-challenge games. -/
def AbortReductionV [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand] (ε_real ε_ideal : ℚ) : Prop :=
  0 ≤ ε_real ∧ 0 ≤ ε_ideal ∧
  ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) -
      mean (middleRealAbortV P h V B outputs fs ab adv x w)| ≤ ε_real ∧
    |mean (middleIdealAbortV P h V B outputs fs ab adv x hx) -
      mean (idealTestV h V B outputs fs adv x hx)| ≤ ε_ideal

end Games

/-- Theorem A with the pole term. -/
theorem zkfs_of_hvzk_onV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hh : HVZK_onV (Bat := Bat) P h V B outputs x)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_real ε_ideal ε_pole : ℚ)
    (hr : AbortReductionV P h V B outputs fs ab x ε_real ε_ideal)
    (hpole : ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
      eventMass (fun ct : (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) =>
        poleBad P h V ab adv x w ct.1) ≤ ε_pole) :
    ZK_FSV h V B outputs fs x (ε_real + ε_ideal + ε_pole) := by
  intro hx adv w hw
  obtain ⟨_, _, hb⟩ := hr
  obtain ⟨hreal, hideal⟩ := hb hx adv w hw
  have hmid := real_hybrid_eq P h V B outputs fs ab adv x hx w hw hh
  have hbad := (hybrid_ideal_le P h V B outputs fs ab adv x hx w).trans (hpole adv w hw)
  rw [hmid] at hreal
  have t1 := abs_sub_le (mean (realTest h B outputs fs adv x w))
    (mean (hybridAbortV P h V B outputs fs ab adv x hx w))
    (mean (middleIdealAbortV P h V B outputs fs ab adv x hx))
  have t2 := abs_sub_le (mean (realTest h B outputs fs adv x w))
    (mean (middleIdealAbortV P h V B outputs fs ab adv x hx))
    (mean (idealTestV h V B outputs fs adv x hx))
  linarith

/-! ### The named oracle-programming terms -/

def RealAbortCouplingV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.RealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_hit ε_coll : ℚ) : Prop :=
  ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    ∃ (cp : Coupling fs.RealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (Hit Coll : cp.S → Prop),
      (∀ s, ¬ Hit s → ¬ Coll s →
        realTest h B outputs fs adv x w (cp.toR s) =
          middleRealAbortV P h V B outputs fs ab adv x w (cp.toM s)) ∧
      eventMass Hit ≤ ε_hit ∧ eventMass Coll ≤ ε_coll

def IdealAbortCouplingV (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_prog : ℚ) : Prop :=
  ∀ (hx : InLanguage h x) (adv : fs.Adversary),
    ∃ (cp : Coupling fs.IdealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (Prog : cp.S → Prop),
      (∀ s, ¬ Prog s →
        middleIdealAbortV P h V B outputs fs ab adv x hx (cp.toM s) =
          idealTestV h V B outputs fs adv x hx (cp.toR s)) ∧
      eventMass Prog ≤ ε_prog

theorem abortReductionV_of_couplings (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_hit ε_coll ε_prog : ℚ)
    (h0 : 0 ≤ ε_hit) (h1 : 0 ≤ ε_coll) (h2 : 0 ≤ ε_prog)
    (hreal : RealAbortCouplingV P h V B outputs fs ab x ε_hit ε_coll)
    (hideal : IdealAbortCouplingV P h V B outputs fs ab x ε_prog) :
    AbortReductionV P h V B outputs fs ab x (ε_hit + ε_coll) ε_prog := by
  refine ⟨by linarith, h2, ?_⟩
  intro hx adv w hw
  have hbit : ∀ c k v, 0 ≤ bit (fs.observe adv (ab.extend adv x c k v)) ∧
      bit (fs.observe adv (ab.extend adv x c k v)) ≤ 1 :=
    fun _ _ _ => ⟨bit_nonneg _, bit_le_one _⟩
  have hfail : ∀ c, 0 ≤ bit (fs.observe adv (ab.fail adv x c)) ∧
      bit (fs.observe adv (ab.fail adv x c)) ≤ 1 :=
    fun _ => ⟨bit_nonneg _, bit_le_one _⟩
  constructor
  · obtain ⟨cp, Hit, Coll, hag, hH, hC⟩ := hreal adv w hw
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
  · obtain ⟨cp, Prog, hag, hP⟩ := hideal hx adv
    rw [← cp.meanR (idealTestV h V B outputs fs adv x hx),
      ← cp.meanM (middleIdealAbortV P h V B outputs fs ab adv x hx)]
    have hb := until_bad (fun s => middleIdealAbortV P h V B outputs fs ab adv x hx (cp.toM s))
      (fun s => idealTestV h V B outputs fs adv x hx (cp.toR s))
      (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
      Prog hag
    linarith

/-- Theorem B with the pole term: error `ε_hit + ε_coll + ε_prog + N·q`. -/
theorem zkfs_of_hvzk_onV_terms (P : Challenges K → Prop) (h : HonestProver K)
    (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hh : HVZK_onV (Bat := Bat) P h V B outputs x)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_hit ε_coll ε_prog q : ℚ)
    (h0 : 0 ≤ ε_hit) (h1 : 0 ≤ ε_coll) (h2 : 0 ≤ ε_prog)
    (hreal : RealAbortCouplingV P h V B outputs fs ab x ε_hit ε_coll)
    (hideal : IdealAbortCouplingV P h V B outputs fs ab x ε_prog)
    (hq : ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
      eventMass (attemptBad P h V ab adv x w) ≤ q) :
    ZK_FSV h V B outputs fs x (ε_hit + ε_coll + ε_prog + ab.N * q) :=
  zkfs_of_hvzk_onV P h V B outputs fs x hh ab (ε_hit + ε_coll) ε_prog (ab.N * q)
    (abortReductionV_of_couplings P h V B outputs fs ab x ε_hit ε_coll ε_prog h0 h1 h2 hreal hideal)
    (fun adv w hw => poleBad_mass_le P h V fs ab adv x w q (hq adv w hw))

#print axioms mean_sum
#print axioms eventMass_mono
#print axioms eventMass_exists_le
#print axioms eventMass_fst
#print axioms firstGood_congr
#print axioms simV
#print axioms HVZK_onV
#print axioms MaskImageOnV
#print axioms maskImageOnV_mono
#print axioms maskImageOn_point
#print axioms view_restrict
#print axioms hvzk_on_of_V
#print axioms real_hybrid_eq
#print axioms hybrid_ideal_le
#print axioms poleBad_mass_le
#print axioms AbortReductionV
#print axioms zkfs_of_hvzk_onV
#print axioms RealAbortCouplingV
#print axioms IdealAbortCouplingV
#print axioms abortReductionV_of_couplings
#print axioms zkfs_of_hvzk_onV_terms
end R0Z.HvzkV
