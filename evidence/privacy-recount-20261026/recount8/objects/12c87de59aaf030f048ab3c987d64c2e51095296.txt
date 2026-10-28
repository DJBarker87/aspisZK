import R0Z.FsAbort
import R0Z.FsAbortBounds

/-! ZF1a/b on R1 (DESIGN-ZF1-COUPLINGS-R1 §3–§8). The abort couplings of
`FsAbort` (`RealAbortCoupling`, `IdealAbortCoupling`) for the retrying R1
prover, with the charged events made concrete as address events over the
coupling space:

* `Hit`  := `HitEv`: some charged prover read (any read of a discarded
  attempt, or an unpublished read of the accepted attempt) is read by the
  adversary;
* `Coll` := `CollEv ∨ exh`: two prover reads, at least one private, have the
  same address, or a mask limb exhausted its 16 rejection tries;
* `Prog` := `CollEv` on the ideal coupling space (two programmed reads with
  the same address).

`R1RealModel` / `R1IdealModel` bundle the named hypotheses: the couplings
themselves (the lazy-programming law), agreement of the games outside the
events (protocol refinement of the Rust prover to the Lean view), the
per-read freshness facts `HitFresh` / `PairFresh` (the designated fields of
the R1 byte layout), and the exhaustion mass. From them the event masses are
PROVED (`FsAbortBounds`), giving ZK_FS with error
`M*q/Umin + (M*M/Umin + εexh) + Mi*Mi/Umin`, and `≤ 2^-166` at N = 8
(`M = Mi = 8 * 2^21` positions), `q = 2^64`, `Umin = 2^255`. -/
set_option autoImplicit false
noncomputable section
namespace R0Z.FsAbortR1
open R0P R0Z.JointView R0Z.FsStatement R0Z.Shift R0Z.FsGood R0Z.FsAbort
attribute [local instance] Classical.propDecidable

/-- `FsAbort.eventMass` and `FsAbortBounds.mass` are the same constant body. -/
theorem eventMass_eq_mass {S : Type} [Fintype S] (E : S → Prop) :
    eventMass E = FsAbortBounds.mass E := rfl

/-! ### R1 read counts (design §1.1, §1.5; source counts, not instrumented) -/

/-- init + rows 0..26 (absorb, squeeze, advance) + reseed + rows 27..30 +
row 31 (absorb and eight squeeze/advance pairs) + row 32. -/
def r1TranscriptReads : ℕ := 1 + 27 * 3 + 1 + 4 * 3 + (1 + 16) + 3

theorem r1TranscriptReads_eq : r1TranscriptReads = 115 := by
  norm_num [r1TranscriptReads]

/-- Per-attempt reads: salts, leaves, 8-ary nodes (C1, C2, folded), expander
blocks (worst case), transcript, seeds/binding/context. -/
def r1AttemptReadBound : ℕ :=
  (2 * 2 ^ 18 + 2 ^ 16) + (2 * 2 ^ 18 + 2 ^ 16) + (2 * 2 ^ 18 / 7 + 2 ^ 16) + 2 ^ 18 +
    r1TranscriptReads + 64

theorem r1AttemptReadBound_le : r1AttemptReadBound ≤ 2 ^ 21 := by
  norm_num [r1AttemptReadBound, r1TranscriptReads]

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [HonestView.BatchedLayer K Bat]

/-! ### The real coupling (Hit, Coll) -/

/-- Named hypotheses of the R1 real coupling, for every adversary and witness:
a coupling `cp` of the real randomness with the abort-middle coins (HYP:
lazy-programming law); `M` prover positions with addresses `addr`, a static
`priv` flag and a charging event; `q` adversary reads `qry`; agreement of
`realTest` and `middleRealAbort` outside `HitEv ∨ (CollEv ∨ exh)` (HYP:
refinement); `HitFresh` for every charged position and read, `PairFresh` for
every private-involving pair (HYP: R1 byte layout, design §1.4); and the
exhaustion mass. -/
def R1RealModel (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.RealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (M q Umin : ℕ) (εexh : ℚ) : Prop :=
  ∀ (adv : fs.Adversary) (w : h.Instance), h.public w = x.1 →
    ∃ (cp : Coupling fs.RealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (charged : Fin M → cp.S → Prop) (priv : Fin M → Prop)
      (addr : Fin M → cp.S → Bytes) (qry : Fin q → cp.S → Bytes) (exh : cp.S → Prop),
      (∀ s, ¬ FsAbortBounds.HitEv M q charged qry addr s →
          ¬ (FsAbortBounds.CollEv M priv addr s ∨ exh s) →
        realTest h B outputs fs adv x w (cp.toR s) =
          middleRealAbort P h B outputs fs ab adv x w (cp.toM s)) ∧
      (∀ j i, FsAbortBounds.HitFresh (charged j) (qry i) (addr j) Umin) ∧
      (∀ j j', j < j' → (priv j ∨ priv j') →
        FsAbortBounds.PairFresh (addr j) (addr j') Umin ∨
          FsAbortBounds.PairFresh (addr j') (addr j) Umin) ∧
      FsAbortBounds.mass exh ≤ εexh

omit [DecidableEq K] in
theorem realAbortCoupling_of_R1 (P : Challenges K → Prop) (h : HonestProver K)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.RealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (M q Umin : ℕ) (εexh : ℚ) (hU : 0 < Umin)
    (hm : R1RealModel P h B outputs fs ab x M q Umin εexh) :
    RealAbortCoupling P h B outputs fs ab x ((M : ℚ) * q / Umin)
      ((M : ℚ) * M / Umin + εexh) := by
  intro adv w hw
  obtain ⟨cp, charged, priv, addr, qry, exh, hag, hhit, hpair, hexh⟩ := hm adv w hw
  refine ⟨cp, FsAbortBounds.HitEv M q charged qry addr,
    fun s => FsAbortBounds.CollEv M priv addr s ∨ exh s, hag, ?_, ?_⟩
  · rw [eventMass_eq_mass]
    exact FsAbortBounds.hitEv_mass_fresh M q Umin hU charged qry addr hhit
  · rw [eventMass_eq_mass]
    calc FsAbortBounds.mass (fun s => FsAbortBounds.CollEv M priv addr s ∨ exh s)
        ≤ FsAbortBounds.mass (FsAbortBounds.CollEv M priv addr) + FsAbortBounds.mass exh :=
          FsAbortBounds.mass_or_le _ _
      _ ≤ (M : ℚ) * M / Umin + εexh :=
          add_le_add (FsAbortBounds.collEv_mass_fresh M Umin hU priv addr hpair) hexh

/-! ### The ideal coupling (Prog) -/

/-- Named hypotheses of the R1 ideal coupling: a coupling of the ideal
randomness with the abort-middle coins (HYP), `M` programmed positions,
agreement outside `CollEv` (HYP), and `PairFresh` for private-involving pairs. -/
def R1IdealModel (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (M Umin : ℕ) : Prop :=
  ∀ (hx : InLanguage h x) (adv : fs.Adversary),
    ∃ (cp : Coupling fs.IdealRand ((Fin ab.N → ab.Coins) × (Fin ab.N → Tape K F)))
      (priv : Fin M → Prop) (addr : Fin M → cp.S → Bytes),
      (∀ s, ¬ FsAbortBounds.CollEv M priv addr s →
        middleIdealAbort P h B outputs fs ab adv x hx (cp.toM s) =
          idealTest h B outputs fs adv x hx (cp.toR s)) ∧
      (∀ j j', j < j' → (priv j ∨ priv j') →
        FsAbortBounds.PairFresh (addr j) (addr j') Umin ∨
          FsAbortBounds.PairFresh (addr j') (addr j) Umin)

omit [DecidableEq K] in
theorem idealAbortCoupling_of_R1 (P : Challenges K → Prop) (h : HonestProver K)
    (B : PackBasis F) (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F) [Fintype fs.IdealRand]
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (x : Statement K CommitHandle) (M Umin : ℕ) (hU : 0 < Umin)
    (hm : R1IdealModel P h B outputs fs ab x M Umin) :
    IdealAbortCoupling P h B outputs fs ab x ((M : ℚ) * M / Umin) := by
  intro hx adv
  obtain ⟨cp, priv, addr, hag, hpair⟩ := hm hx adv
  refine ⟨cp, FsAbortBounds.CollEv M priv addr, hag, ?_⟩
  rw [eventMass_eq_mass]
  exact FsAbortBounds.collEv_mass_fresh M Umin hU priv addr hpair

/-! ### Composition and the numbers -/

omit [Fintype K] [DecidableEq K] in
theorem zkfs_mono (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (ε ε' : ℚ)
    (hz : ZK_FS h B outputs fs x ε) (hle : ε ≤ ε') : ZK_FS h B outputs fs x ε' :=
  fun hx adv w hw => (hz hx adv w hw).trans hle

/-- ZK_FS for the retrying R1 prover from HVZK on `P` and the two R1 models. -/
theorem zkfs_R1_abort (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hh : HVZK_on (Bat := Bat) P h B outputs x)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (M Mi q Umin : ℕ) (εexh : ℚ) (hU : 0 < Umin) (he : 0 ≤ εexh)
    (hr : R1RealModel P h B outputs fs ab x M q Umin εexh)
    (hi : R1IdealModel P h B outputs fs ab x Mi Umin) :
    ZK_FS h B outputs fs x
      ((M : ℚ) * q / Umin + ((M : ℚ) * M / Umin + εexh) + (Mi : ℚ) * Mi / Umin) :=
  zkfs_of_hvzk_on_abort_terms P h B outputs fs x hh ab
    ((M : ℚ) * q / Umin) ((M : ℚ) * M / Umin + εexh) ((Mi : ℚ) * Mi / Umin)
    (by positivity) (add_nonneg (by positivity) he) (by positivity)
    (realAbortCoupling_of_R1 P h B outputs fs ab x M q Umin εexh hU hr)
    (idealAbortCoupling_of_R1 P h B outputs fs ab x Mi Umin hU hi)

/-- N = 8 attempts of at most 2^21 reads, q = 2^64 adversary reads, designated
fields of at least 2^255 values; the exhaustion slot is 2^-250, a loose upper
bound of 8 · 2^17 limbs · 2^-496 (design §5.4). -/
theorem r1_error_N8 :
    ((8 * 2 ^ 21 : ℕ) : ℚ) * ((2 ^ 64 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
      (((8 * 2 ^ 21 : ℕ) : ℚ) * ((8 * 2 ^ 21 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (1 / 2 ^ 250 : ℚ)) +
      ((8 * 2 ^ 21 : ℕ) : ℚ) * ((8 * 2 ^ 21 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) ≤
    1 / 2 ^ 166 := by
  norm_num

theorem zkfs_R1_abort_N8 (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle) (hh : HVZK_on (Bat := Bat) P h B outputs x)
    (ab : AbortBridge K CommitHandle Aux Bat fs.Adversary)
    (hr : R1RealModel P h B outputs fs ab x (8 * 2 ^ 21) (2 ^ 64) (2 ^ 255)
      (1 / 2 ^ 250))
    (hi : R1IdealModel P h B outputs fs ab x (8 * 2 ^ 21) (2 ^ 255)) :
    ZK_FS h B outputs fs x (1 / 2 ^ 166) :=
  zkfs_mono h B outputs fs x _ _
    (zkfs_R1_abort P h B outputs fs x hh ab (8 * 2 ^ 21) (8 * 2 ^ 21) (2 ^ 64) (2 ^ 255)
      (1 / 2 ^ 250) (by positivity) (by positivity) hr hi)
    r1_error_N8

#print axioms eventMass_eq_mass
#print axioms r1TranscriptReads_eq
#print axioms r1AttemptReadBound_le
#print axioms R1RealModel
#print axioms realAbortCoupling_of_R1
#print axioms R1IdealModel
#print axioms idealAbortCoupling_of_R1
#print axioms zkfs_mono
#print axioms zkfs_R1_abort
#print axioms r1_error_N8
#print axioms zkfs_R1_abort_N8
end R0Z.FsAbortR1
