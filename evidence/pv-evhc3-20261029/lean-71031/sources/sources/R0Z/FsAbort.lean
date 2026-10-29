import R0Z.FsGood

/-! ZF1-abort (D29): honest-prover rejection on a public challenge predicate.
The prover retries with fresh coins until the drawn challenge satisfies `P`,
up to a cap `N`, and publishes only the accepted attempt (or the failure
output). The middle experiments then pass only `P`-challenges to the view
and the simulator, so `HVZK_on P` makes them equal: no `badMass P` term.
The remaining error is the abort-aware ROM reduction, split into named
identical-until-bad events (discarded-point hits, prover-address
collisions, programming failures) whose bounds are payload facts and enter
as hypotheses. The core (`retryTest`, `retry_means_eq`) is generic in the
coin, tape and view types. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.FsAbort
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood
attribute [local instance] Classical.propDecidable

/-! ### Generic core: uniform means -/

theorem mean_equiv {R S : Type} [Fintype R] [Fintype S] (e : R ≃ S) (f : R → ℚ) :
    mean f = mean (fun s => f (e.symm s)) := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e f (fun s => f (e.symm s)) (fun r => by simp)

theorem mean_const {R : Type} [Fintype R] [Nonempty R] (c : ℚ) :
    mean (fun _ : R => c) = c := by
  unfold mean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h : (Fintype.card R : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

/-- A test of one coordinate of an independent tuple has the coordinate's mean:
the other attempts' tapes are marginalised out. -/
theorem mean_eval {N : Nat} {T : Type} [Fintype T] [Nonempty T] (k : Fin N) (g : T → ℚ) :
    mean (fun ts : Fin N → T => g (ts k)) = mean g := by
  rw [mean_equiv (Equiv.funSplitAt k T)]
  have hk : ∀ p : T × ({j // j ≠ k} → T), ((Equiv.funSplitAt k T).symm p) k = p.1 := by
    intro p
    have he := congrArg Prod.fst ((Equiv.funSplitAt k T).apply_symm_apply p)
    exact he
  simp only [hk]
  rw [LawTransport.mean_product]
  simp only [mean_const]

theorem mean_add' {R : Type} [Fintype R] (f g : R → ℚ) :
    mean (fun r => f r + g r) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

/-! ### Generic core: the retry loop -/

/-- The least attempt whose coins satisfy `Pd`, or `none` (failure exit). -/
def firstGood {C : Type} (Pd : C → Prop) {N : Nat} (c : Fin N → C) : Option (Fin N) :=
  if h : (Finset.univ.filter (fun k => Pd (c k))).Nonempty then
    some ((Finset.univ.filter (fun k => Pd (c k))).min' h)
  else none

theorem firstGood_spec {C : Type} (Pd : C → Prop) {N : Nat} (c : Fin N → C) (k : Fin N)
    (hk : firstGood Pd c = some k) : Pd (c k) := by
  unfold firstGood at hk
  by_cases h : (Finset.univ.filter (fun j => Pd (c j))).Nonempty
  · rw [dif_pos h] at hk
    have he := Option.some.inj hk
    have hm := Finset.min'_mem _ h
    rw [he] at hm
    exact (Finset.mem_filter.mp hm).2
  · rw [dif_neg h] at hk
    cases hk

theorem firstGood_least {C : Type} (Pd : C → Prop) {N : Nat} (c : Fin N → C) (k : Fin N)
    (hk : firstGood Pd c = some k) (j : Fin N) (hj : Pd (c j)) : k ≤ j := by
  unfold firstGood at hk
  by_cases h : (Finset.univ.filter (fun i => Pd (c i))).Nonempty
  · rw [dif_pos h] at hk
    rw [← Option.some.inj hk]
    exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  · rw [dif_neg h] at hk
    cases hk

theorem firstGood_none {C : Type} (Pd : C → Prop) {N : Nat} (c : Fin N → C)
    (hn : firstGood Pd c = none) (k : Fin N) : ¬ Pd (c k) := by
  intro hk
  unfold firstGood at hn
  have h : (Finset.univ.filter (fun j => Pd (c j))).Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  rw [dif_pos h] at hn
  cases hn

/-- Observer bit of the retry loop: attempt coins `ct.1`, attempt tapes `ct.2`.
Only the accepted attempt's tape and published value reach `ext`; `ext` and
`fail` may read every attempt's coins. -/
def retryTest {C T V : Type} (N : Nat) (Pd : C → Prop) (pub : C → T → V)
    (ext : (Fin N → C) → Fin N → V → ℚ) (fail : (Fin N → C) → ℚ) :
    (Fin N → C) × (Fin N → T) → ℚ :=
  fun ct => match firstGood Pd ct.1 with
    | none => fail ct.1
    | some k => ext ct.1 k (pub (ct.1 k) (ct.2 k))

theorem retryTest_bounds {C T V : Type} (N : Nat) (Pd : C → Prop) (pub : C → T → V)
    (ext : (Fin N → C) → Fin N → V → ℚ) (fail : (Fin N → C) → ℚ)
    (he : ∀ c k v, 0 ≤ ext c k v ∧ ext c k v ≤ 1) (hf : ∀ c, 0 ≤ fail c ∧ fail c ≤ 1)
    (ct : (Fin N → C) × (Fin N → T)) :
    0 ≤ retryTest N Pd pub ext fail ct ∧ retryTest N Pd pub ext fail ct ≤ 1 := by
  unfold retryTest
  split
  · exact hf _
  · exact he _ _ _

/-- The abort-aware middle step: if the published values agree in law on every
accepted coin, the retry loops have equal means. No mass of rejected coins. -/
theorem retry_means_eq {C T V : Type} [Fintype C] [Fintype T] [Nonempty T] (N : Nat)
    (Pd : C → Prop) (pub₁ pub₂ : C → T → V)
    (ext : (Fin N → C) → Fin N → V → ℚ) (fail : (Fin N → C) → ℚ)
    (hEq : ∀ c, Pd c → EqualLaws (pub₁ c) (pub₂ c)) :
    mean (retryTest N Pd pub₁ ext fail) = mean (retryTest N Pd pub₂ ext fail) := by
  rw [LawTransport.mean_product, LawTransport.mean_product]
  apply congrArg mean
  funext c
  rcases hk : firstGood Pd c with _ | k
  · simp only [retryTest, hk]
  · simp only [retryTest, hk]
    exact (mean_eval k (fun t => ext c k (pub₁ (c k) t))).trans
      ((LawTransport.mean_eq_of_equalLaws _ _ (ext c k)
        (hEq _ (firstGood_spec Pd c k hk))).trans
        (mean_eval k (fun t => ext c k (pub₂ (c k) t))).symm)

/-! ### Generic core: identical until bad -/

def eventMass {S : Type} [Fintype S] (E : S → Prop) : ℚ :=
  mean (fun s => if E s then 1 else 0)

theorem eventMass_or_le {S : Type} [Fintype S] (E E' : S → Prop) :
    eventMass (fun s => E s ∨ E' s) ≤ eventMass E + eventMass E' := by
  unfold eventMass
  rw [← mean_add']
  apply mean_le_mean
  intro s
  by_cases h1 : E s <;> by_cases h2 : E' s <;> simp [h1, h2]

theorem until_bad {S : Type} [Fintype S] (f g : S → ℚ)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ 1) (hg : ∀ s, 0 ≤ g s ∧ g s ≤ 1)
    (E : S → Prop) (hagree : ∀ s, ¬ E s → f s = g s) :
    |mean f - mean g| ≤ eventMass E := by
  unfold eventMass
  rw [mean_sub]
  refine (abs_mean_le _).trans (mean_le_mean _ _ ?_)
  intro s
  by_cases hE : E s
  · rw [if_pos hE]
    have h1 := hf s
    have h2 := hg s
    rw [abs_sub_le_iff]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · rw [if_neg hE, hagree s hE, sub_self, abs_zero]

/-- A finite common space carrying uniform maps to two finite uniform spaces. -/
structure Coupling (R M : Type) [Fintype R] [Fintype M] where
  S : Type
  finS : Fintype S
  nonemptyS : Nonempty S
  toR : S → R
  toM : S → M
  meanR : ∀ f : R → ℚ, @mean S finS (fun s => f (toR s)) = mean f
  meanM : ∀ f : M → ℚ, @mean S finS (fun s => f (toM s)) = mean f

attribute [instance] Coupling.finS Coupling.nonemptyS

/-! ### The R0Z specialisation -/

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [HonestView.BatchedLayer K Bat]

/-- Per-attempt bridge coins, a cap `N`, and the extension/failure outputs.
`extend` receives all attempts' coins and the accepted index. -/
structure AbortBridge (K CommitHandle Aux Bat Adv : Type) [Field K] where
  Coins : Type
  finiteCoins : Fintype Coins
  nonemptyCoins : Nonempty Coins
  N : Nat
  draw : Adv → Statement K CommitHandle → Coins → Challenges K
  extend : Adv → Statement K CommitHandle → (Fin N → Coins) → Fin N →
    View K CommitHandle Aux Bat → ROMView K CommitHandle Aux Bat
  fail : Adv → Statement K CommitHandle → (Fin N → Coins) → ROMView K CommitHandle Aux Bat

attribute [instance] AbortBridge.finiteCoins AbortBridge.nonemptyCoins

/-- Host attempt 3501: `Fintype (Tape K F)` is found but not under `Fin n → ·`;
naming it lets the Pi instance close. It is definitionally the inferred one. -/
instance tapeFintype : Fintype (Tape K F) := inferInstance

def middleRealAbort (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (w : h.Instance) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin))
    (fun coin t => view h B outputs x w (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

def middleIdealAbort (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) :
    (Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F) → ℚ :=
  retryTest ab.N (fun coin => P (ab.draw adv x coin))
    (fun coin t => simulator h B outputs x hx (ab.draw adv x coin) t)
    (fun c k v => bit (fs.observe adv (ab.extend adv x c k v)))
    (fun c => bit (fs.observe adv (ab.fail adv x c)))

/-- The middle experiments agree exactly under `HVZK_on P`. -/
theorem middleAbort_means_eq (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (adv : fs.Adversary)
    (x : Statement K CommitHandle) (hx : InLanguage h x) (w : h.Instance)
    (hw : h.public w = x.1) (hh : HVZK_on (Bat := Bat) P h B outputs x) :
    mean (middleRealAbort P h B outputs fs ab adv x w) =
      mean (middleIdealAbort P h B outputs fs ab adv x hx) := by
  haveI : Nonempty (Tape K F) := ⟨(0, 0)⟩
  exact retry_means_eq ab.N _ _ _ _ _ (fun coin hc => hh hx w (ab.draw adv x coin) hc hw)

/-- The abort-aware reduction certificate for a specified abort bridge. -/
def AbortReductionWith (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_real ε_ideal : ℚ) : Prop :=
  0 ≤ ε_real ∧ 0 ≤ ε_ideal ∧
  ∀ (hx : InLanguage h x) (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    |mean (realTest h B outputs fs adv x w) -
      mean (middleRealAbort P h B outputs fs ab adv x w)| ≤ ε_real ∧
    |mean (middleIdealAbort P h B outputs fs ab adv x hx) -
      mean (idealTest h B outputs fs adv x hx)| ≤ ε_ideal

/-- Theorem A: HVZK on `P` plus the abort-aware reduction; no bad-mass term. -/
theorem zkfs_of_hvzk_on_abort (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hh : HVZK_on (Bat := Bat) P h B outputs x)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_real ε_ideal : ℚ)
    (hr : AbortReductionWith P h B outputs fs ab x ε_real ε_ideal) :
    ZK_FS h B outputs fs x (ε_real + ε_ideal) := by
  intro hx adv w hw
  obtain ⟨_, _, hb⟩ := hr
  obtain ⟨hreal, hideal⟩ := hb hx adv w hw
  have hmid := middleAbort_means_eq P h B outputs fs ab adv x hx w hw hh
  rw [hmid] at hreal
  exact (abs_sub_le _ _ _).trans (add_le_add hreal hideal)

theorem hvzk_on_mono (P Q : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hPQ : ∀ ch, P ch → Q ch)
    (hq : HVZK_on (Bat := Bat) Q h B outputs x) : HVZK_on (Bat := Bat) P h B outputs x :=
  fun hx w ch hp hw => hq hx w ch (hPQ ch hp) hw

/-- Mask image on `Good`, rejection on any `P` implying `Good`. -/
theorem zkfs_of_maskImageOn_abort [Fintype Bat] (P : Challenges K → Prop) (h : HonestProver K)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hPG : ∀ ch, P ch → Good ch)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_real ε_ideal : ℚ) :
    MaskImageOn (Bat := Bat) Good h B x → AbortReductionWith P h B outputs fs ab x ε_real ε_ideal →
    ZK_FS h B outputs fs x (ε_real + ε_ideal) :=
  fun hm hr => zkfs_of_hvzk_on_abort P h B outputs fs x
    (hvzk_on_mono P Good h B outputs x hPG (hvzk_on_good h B outputs x hm)) ab ε_real ε_ideal hr

/-! ### The named oracle-programming terms -/

/-- Real side: outside the discarded-point hit `Hit` and the prover-address
collision `Coll`, the real retrying game and the middle game agree. -/
def RealAbortCoupling (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.RealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_hit ε_coll : ℚ) : Prop :=
  ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    ∃ (cp : Coupling fs.RealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (Hit Coll : cp.S → Prop),
      (∀ s, ¬ Hit s → ¬ Coll s →
        realTest h B outputs fs adv x w (cp.toR s) =
          middleRealAbort P h B outputs fs ab adv x w (cp.toM s)) ∧
      eventMass Hit ≤ ε_hit ∧ eventMass Coll ≤ ε_coll

/-- Ideal side: outside the programming failure `Prog`, the middle game and
the rejection-sampling ideal game agree. -/
def IdealAbortCoupling (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_prog : ℚ) : Prop :=
  ∀ (hx : InLanguage h x) (adv : fs.Adversary),
    ∃ (cp : Coupling fs.IdealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (Prog : cp.S → Prop),
      (∀ s, ¬ Prog s →
        middleIdealAbort P h B outputs fs ab adv x hx (cp.toM s) =
          idealTest h B outputs fs adv x hx (cp.toR s)) ∧
      eventMass Prog ≤ ε_prog

theorem abortReduction_of_couplings (P : Challenges K → Prop) (h : HonestProver K)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (ε_hit ε_coll ε_prog : ℚ)
    (h0 : 0 ≤ ε_hit) (h1 : 0 ≤ ε_coll) (h2 : 0 ≤ ε_prog)
    (hreal : RealAbortCoupling P h B outputs fs ab x ε_hit ε_coll)
    (hideal : IdealAbortCoupling P h B outputs fs ab x ε_prog) :
    AbortReductionWith P h B outputs fs ab x (ε_hit + ε_coll) ε_prog := by
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
      ← cp.meanM (middleRealAbort P h B outputs fs ab adv x w)]
    have hb := until_bad (fun s => realTest h B outputs fs adv x w (cp.toR s))
      (fun s => middleRealAbort P h B outputs fs ab adv x w (cp.toM s))
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
      (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _)
      (fun s => Hit s ∨ Coll s)
      (fun s hs => hag s (fun hh => hs (Or.inl hh)) (fun hh => hs (Or.inr hh)))
    have ho := eventMass_or_le Hit Coll
    linarith
  · obtain ⟨cp, Prog, hag, hP⟩ := hideal hx adv
    rw [← cp.meanR (idealTest h B outputs fs adv x hx),
      ← cp.meanM (middleIdealAbort P h B outputs fs ab adv x hx)]
    have hb := until_bad (fun s => middleIdealAbort P h B outputs fs ab adv x hx (cp.toM s))
      (fun s => idealTest h B outputs fs adv x hx (cp.toR s))
      (fun s => retryTest_bounds _ _ _ _ _ hbit hfail _)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
      Prog hag
    linarith

/-- Theorem B: ZK_FS for the retrying prover with error equal to the three
named oracle-programming terms. No `badMass P` and no failure-exit term. -/
theorem zkfs_of_hvzk_on_abort_terms (P : Challenges K → Prop) (h : HonestProver K)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hh : HVZK_on (Bat := Bat) P h B outputs x)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_hit ε_coll ε_prog : ℚ)
    (h0 : 0 ≤ ε_hit) (h1 : 0 ≤ ε_coll) (h2 : 0 ≤ ε_prog)
    (hreal : RealAbortCoupling P h B outputs fs ab x ε_hit ε_coll)
    (hideal : IdealAbortCoupling P h B outputs fs ab x ε_prog) :
    ZK_FS h B outputs fs x (ε_hit + ε_coll + ε_prog) :=
  zkfs_of_hvzk_on_abort P h B outputs fs x hh ab (ε_hit + ε_coll) ε_prog
    (abortReduction_of_couplings P h B outputs fs ab x ε_hit ε_coll ε_prog h0 h1 h2 hreal hideal)

#print axioms mean_equiv
#print axioms mean_const
#print axioms mean_eval
#print axioms mean_add'
#print axioms firstGood_spec
#print axioms firstGood_least
#print axioms firstGood_none
#print axioms retryTest_bounds
#print axioms retry_means_eq
#print axioms eventMass_or_le
#print axioms until_bad
#print axioms middleAbort_means_eq
#print axioms AbortReductionWith
#print axioms zkfs_of_hvzk_on_abort
#print axioms hvzk_on_mono
#print axioms zkfs_of_maskImageOn_abort
#print axioms RealAbortCoupling
#print axioms IdealAbortCoupling
#print axioms abortReduction_of_couplings
#print axioms zkfs_of_hvzk_on_abort_terms
end R0Z.FsAbort
