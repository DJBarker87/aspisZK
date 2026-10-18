import R0Z.SilentReduction
import R0Z.FsAbort

/-! J0 (DESIGN-ii-prime §1.4, §1.5, §4; DESIGN-R1-PRIVACY-MODEL §3.5; LOG D24.1):
the validity restriction for clause (ii′).

* `HonestValid pub B t ch`: at the payload trace `u = actual pub B t ch 0`,
  every production lane vanishes on the Boolean rows and the two H1 helper
  sums (all rows, inactive rows) are zero.  It reads only the semantic layer,
  so it is the same for every batched block `Bat`.
* `HonestProver.restrict h V`: the prover on the instances satisfying `V`.
  `MaskImageOn`, `hvzk_on_of` and the FsAbort theorems are generic in the
  prover, so they apply verbatim to `h.restrict V` (corollaries below).
* `iota` (initial sum minus `.maskSum`) and `.inactiveSum` vanish on the
  whole tape image `A`; on `cTilde` they equal the Boolean sum of the original
  terminal and γ²⁶ times the inactive helper sum, and both are zero for a
  valid instance (`iota_cTilde_zero`, `inactive_cTilde_zero`).
* `not_iiPrime_witness`: two witnesses with different `iota (cTilde ·)` are
  never related by `range A` (the §1.4 obstruction, as an implication).

Builder completeness (honest builds are `HonestValid`) is J0b and is not
asserted here.  No row set is enumerated: the only concrete evaluation is the
membership of row 1023 in the inactive set, one entry of a 64-entry table. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.ZkStatement.HonestProver

/-- DESIGN-ii-prime §1.5: the prover restricted to the instances satisfying `V`. -/
def restrict {K : Type} (h : HonestProver K) (V : h.Instance → Prop) : HonestProver K :=
  ⟨{w // V w}, h.transport, fun w => h.public w.1, fun w => h.build w.1⟩

end R0Z.ZkStatement.HonestProver

namespace R0Z.HonestValid
open R0P R0P.Sumcheck R0P.SemSource R0P.SemDegree R0Z.MaskLayout R0Z.HonestView
  R0Z.Partition R0Z.D12 R0Z.Shift Polynomial

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {Bat : Type} [BatchedLayer K Bat]

/-! ### Row 1023 is copy-inactive (DESIGN-ii-prime P6) -/

/-- One entry of the 64-entry mask table: `copyActiveRowMasks 63 = 1749`,
whose bit 15 is clear. -/
theorem inactive_1023 : (1023 : Fin 1024) ∈ copyInactiveRows := by
  rw [R0Z.TerminalEligible.mem_inactive]
  have h63 : copyActiveRowMasks 63 = 1749 := by unfold copyActiveRowMasks; rfl
  change ¬ (copyActiveRowMasks 63).testBit 15 = true
  rw [h63]
  decide

attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

/-! ### The validity predicate and the restricted prover -/

/-- DESIGN-ii-prime §1.5: validity of the payload trace `u = actual pub B t ch 0`
at the semantic challenges `λ = ch.sem 0`, `χ = ch.sem 1`. -/
def HonestValid (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K) : Prop :=
  (∀ i b, laneOf (PayloadSplit.actual pub B t ch 0) pub (ch.sem 0) (ch.sem 1) B i b = 0) ∧
  (∑ r, PayloadSplit.actual pub B t ch 0 26 r = 0) ∧
  (∑ r ∈ copyInactiveRows, PayloadSplit.actual pub B t ch 0 26 r = 0)

/-- DESIGN-R1-PRIVACY-MODEL §3.5: valid for every challenge satisfying `P`. -/
def ValidOn (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) : h.Instance → Prop :=
  fun w => ∀ ch, P ch → HonestValid x.1 B (h.build w) ch

/-- DESIGN-ii-prime §1.5: clause (ii′) for valid witnesses. -/
def IIPrimeValid (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) : Prop :=
  ∀ ch, P ch → ∀ w w', h.public w = x.1 → h.public w' = x.1 →
    HonestValid x.1 B (h.build w) ch → HonestValid x.1 B (h.build w') ch →
    cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch ∈ LinearMap.range (A h.transport B ch)

section Restrict
variable (h : HonestProver K) (V : h.Instance → Prop)

theorem restrict_public (w : (ZkStatement.HonestProver.restrict h V).Instance) :
    (ZkStatement.HonestProver.restrict h V).public w = h.public w.1 := rfl

theorem restrict_build (w : (ZkStatement.HonestProver.restrict h V).Instance) :
    (ZkStatement.HonestProver.restrict h V).build w = h.build w.1 := rfl

theorem restrict_transport :
    (ZkStatement.HonestProver.restrict h V).transport = h.transport := rfl

theorem sRem_restrict (B : PackBasis F) (x : Statement K CommitHandle)
    (w : (ZkStatement.HonestProver.restrict h V).Instance) (ch : Challenges K) (n : N K F) :
    sRem (Bat := Bat) (ZkStatement.HonestProver.restrict h V) B x w ch n = sRem h B x w.1 ch n := rfl

theorem cTilde_restrict (B : PackBasis F) (x : Statement K CommitHandle)
    (w : (ZkStatement.HonestProver.restrict h V).Instance) (ch : Challenges K) :
    cTilde (Bat := Bat) (ZkStatement.HonestProver.restrict h V) B x w ch = cTilde h B x w.1 ch := rfl

theorem inLanguage_restrict (x : Statement K CommitHandle) :
    JointView.InLanguage (ZkStatement.HonestProver.restrict h V) x ↔ ∃ w, V w ∧ h.public w = x.1 :=
  ⟨fun ⟨w, hw⟩ => ⟨w.1, w.2, hw⟩, fun ⟨w, hv, hw⟩ => ⟨⟨w, hv⟩, hw⟩⟩

/-- `MaskImageOn` of the restricted prover, unfolded: both clauses on the
instances satisfying `V`. -/
theorem maskImageOn_restrict_iff (P : Challenges K → Prop) (B : PackBasis F)
    (x : Statement K CommitHandle) :
    MaskImageOn (Bat := Bat) P (ZkStatement.HonestProver.restrict h V) B x ↔
      (∀ ch, P ch → ∀ w n, V w → h.public w = x.1 →
        sRem (Bat := Bat) h B x w ch n ∈ LinearMap.range ((A h.transport B ch).comp inlM)) ∧
      (∀ ch, P ch → ∀ w w', V w → V w' → h.public w = x.1 → h.public w' = x.1 →
        cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch ∈ LinearMap.range (A h.transport B ch)) :=
  ⟨fun hm => ⟨fun ch hP w n hv hw => hm.1 ch hP ⟨w, hv⟩ n hw,
      fun ch hP w w' hv hv' hw hw' => hm.2 ch hP ⟨w, hv⟩ ⟨w', hv'⟩ hw hw'⟩,
    fun hm => ⟨fun ch hP w n hw => hm.1 ch hP w.1 n w.2 hw,
      fun ch hP w w' hw hw' => hm.2 ch hP w.1 w'.1 w.2 w'.2 hw hw'⟩⟩

end Restrict

/-- DESIGN-ii-prime §2.5 composition: clause (i′) for all witnesses and the
valid form of (ii′) give `MaskImageOn` for the prover restricted to `ValidOn`. -/
theorem maskImageOn_restrict_of (P : Challenges K → Prop) (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle)
    (hi : ∀ ch, P ch → ∀ w n, h.public w = x.1 →
      sRem (Bat := Bat) h B x w ch n ∈ LinearMap.range ((A h.transport B ch).comp inlM))
    (hii : IIPrimeValid (Bat := Bat) P h B x) :
    MaskImageOn (Bat := Bat) P (ZkStatement.HonestProver.restrict h (ValidOn P h B x)) B x :=
  (maskImageOn_restrict_iff h (ValidOn P h B x) P B x).2
    ⟨fun ch hP w n _ hw => hi ch hP w n hw,
      fun ch hP w w' hv hv' hw hw' => hii ch hP w w' hw hw' (hv ch hP) (hv' ch hP)⟩

/-- `hvzk_on_of` applied verbatim to the restricted prover. -/
theorem hvzk_on_restrict [Fintype Bat] (P : Challenges K → Prop) (h : HonestProver K)
    (V : h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (x : Statement K CommitHandle) :
    MaskImageOn (Bat := Bat) P (ZkStatement.HonestProver.restrict h V) B x →
      HVZK_on (Bat := Bat) P (ZkStatement.HonestProver.restrict h V) B outputs x :=
  hvzk_on_of P (ZkStatement.HonestProver.restrict h V) B outputs x

/-- ZF1-abort Theorem A applied verbatim to the restricted prover. -/
theorem zkfs_restrict_abort [Fintype Bat] (P : Challenges K → Prop) (h : HonestProver K)
    (V : h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FsStatement.FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle)
    (ab : FsAbort.AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_real ε_ideal : ℚ)
    (hm : MaskImageOn (Bat := Bat) P (ZkStatement.HonestProver.restrict h V) B x)
    (hr : FsAbort.AbortReductionWith P (ZkStatement.HonestProver.restrict h V) B outputs fs ab x
      ε_real ε_ideal) :
    FsStatement.ZK_FS (ZkStatement.HonestProver.restrict h V) B outputs fs x (ε_real + ε_ideal) :=
  FsAbort.zkfs_of_hvzk_on_abort P _ B outputs fs x
    (hvzk_on_restrict P h V B outputs x hm) ab ε_real ε_ideal hr

/-- ZF1-abort Theorem B applied verbatim to the restricted prover. -/
theorem zkfs_restrict_abort_terms [Fintype Bat] (P : Challenges K → Prop) (h : HonestProver K)
    (V : h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (fs : FsStatement.FSExperiments K CommitHandle Aux Bat F)
    [Fintype fs.RealRand] [Nonempty fs.RealRand]
    [Fintype fs.IdealRand] [Nonempty fs.IdealRand]
    (x : Statement K CommitHandle)
    (ab : FsAbort.AbortBridge K CommitHandle Aux Bat fs.Adversary) (ε_hit ε_coll ε_prog : ℚ)
    (h0 : 0 ≤ ε_hit) (h1 : 0 ≤ ε_coll) (h2 : 0 ≤ ε_prog)
    (hm : MaskImageOn (Bat := Bat) P (ZkStatement.HonestProver.restrict h V) B x)
    (hreal : FsAbort.RealAbortCoupling P (ZkStatement.HonestProver.restrict h V) B outputs fs ab x
      ε_hit ε_coll)
    (hideal : FsAbort.IdealAbortCoupling P (ZkStatement.HonestProver.restrict h V) B outputs fs ab x
      ε_prog) :
    FsStatement.ZK_FS (ZkStatement.HonestProver.restrict h V) B outputs fs x
      (ε_hit + ε_coll + ε_prog) :=
  FsAbort.zkfs_of_hvzk_on_abort_terms P _ B outputs fs x
    (hvzk_on_restrict P h V B outputs x hm) ab ε_hit ε_coll ε_prog h0 h1 h2 hreal hideal

/-! ### The initial-sum functional ι -/

/-- DESIGN-ii-prime (O1): `ι v = p₀(0) + p₀(1) − v.maskSum`. -/
def iota : Payload K Bat →ₗ[K] K :=
  Chain.evalRound 0 0 + Chain.evalRound 0 1 - Shift.proj .maskSum

theorem iota_apply (v : Payload K Bat) :
    iota v = (Chain.roundPoly 0 v).eval 0 + (Chain.roundPoly 0 v).eval 1 - v .maskSum := by
  simp only [iota, LinearMap.sub_apply, LinearMap.add_apply, Chain.evalRound_apply, Shift.proj_apply]

/-- ι vanishes on `L τ` for every trace (rounds_initial with maskLinear_vdeg). -/
theorem iota_L (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (τ : Trace K) :
    iota (PayloadSplit.L (Bat := Bat) π B ch τ) = 0 := by
  rw [iota_apply, PureRounds.roundPoly_L, Chain.rounds_initial ch _ (maskLinear_vdeg π B τ),
    Chain.bsumB_eq_sum, PureRounds.L_maskSum]
  exact sub_self _

/-- ι vanishes on the whole tape image. -/
theorem iota_A (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (t : T K F) :
    iota (A (Bat := Bat) π B ch t) = 0 := by
  have hA : A (Bat := Bat) π B ch t = PayloadSplit.L π B ch (JointTrace.tapeLinear B t) := rfl
  rw [hA]
  exact iota_L π B ch (JointTrace.tapeLinear B t)

theorem iota_originalRounds (pub : Public K) (B : PackBasis F) (ch : Challenges K) (u : Trace K) :
    iota (PayloadSplit.roundInclusion (Bat := Bat) (PayloadSplit.originalRounds pub B ch u)) =
      bsumB 10 (fun b => fOrig pub B ch u (ofBool b)) := by
  have h0 : PayloadSplit.roundInclusion (Bat := Bat)
      (PayloadSplit.originalRounds pub B ch u) .maskSum = 0 := rfl
  rw [iota_apply, Chain.roundPoly_originalRounds, Chain.rounds_initial ch _ (vdeg_fOrig pub B ch u),
    h0, sub_zero]

theorem iota_dir : iota (dir : Payload K Bat) = 0 := by
  have hm : (dir : Payload K Bat) .maskSum = 0 := rfl
  have h09 : (0 : Fin 10) ≠ 9 := by decide
  simp only [iota_apply, Chain.roundPoly_dir, h09, ↓reduceIte, eval_zero, hm, add_zero, sub_zero]

/-! ### The zero-tape payload -/

/-- `c = L u + O u` at `u = actual x.1 B (h.build w) ch 0` (D12's `hc`). -/
theorem c_eq (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    JointView.c (Bat := Bat) h B x w ch =
      PayloadSplit.L h.transport B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) +
        PayloadSplit.O x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) := by
  have hs : D12.payload (Bat := Bat) h B x w ch 0 =
      PayloadSplit.L h.transport B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) +
        PayloadSplit.O x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) :=
    PayloadSplit.run_split h.transport x.1 B (applyEligible (h.build w) (0 : T K F).2.2) ch
      (aff (0 : T K F))
  have hz : D12.payload (Bat := Bat) h B x w ch 0 = JointView.c h B x w ch :=
    congrArg (JointView.payload h B x w ch) (map_zero Partition.equiv)
  exact hz.symm.trans hs

theorem iota_c (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    iota (JointView.c (Bat := Bat) h B x w ch) =
      bsumB 10 (fun b => fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) (ofBool b)) := by
  rw [c_eq, map_add, iota_L, zero_add]
  exact iota_originalRounds x.1 B ch _

/-- DESIGN-ii-prime §1.4 (O1) on `cTilde`. -/
theorem iota_cTilde (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    iota (cTilde (Bat := Bat) h B x w ch) =
      bsumB 10 (fun b => fOrig x.1 B ch (PayloadSplit.actual x.1 B (h.build w) ch 0) (ofBool b)) := by
  unfold cTilde
  rw [map_sub, map_smul, iota_dir, smul_zero, sub_zero]
  exact iota_c h B x w ch

/-! ### The Boolean sum of the original terminal at a valid trace -/

/-- The 14 pre-sumcheck challenges read from `ch.sem` (λ, χ, θ, zc, μ). -/
def preOf (ch : Challenges K) : Fin 14 → K := fun i => ch.sem ⟨i.val, by omega⟩

/-- `fOrig`'s terminal arguments are exactly `virtualPoly`'s at `preOf ch`. -/
theorem fOrig_eq_virtualPoly (pub : Public K) (B : PackBasis F) (ch : Challenges K)
    (u : Trace K) (a : Fin 10 → K) :
    fOrig pub B ch u a = ch.sem 14 * virtualPoly pub B u (preOf ch) a := rfl

theorem fOrig_ofBool (pub : Public K) (B : PackBasis F) (ch : Challenges K) (u : Trace K)
    (h1 : ∀ i b, laneOf u pub (ch.sem 0) (ch.sem 1) B i b = 0) (b : Fin 10 → Bool) :
    fOrig pub B ch u (ofBool b) = ch.sem 14 * (ch.sem 13 * u 26 (rowOf b) +
      ch.sem 13 ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) *
        u 26 (rowOf b))) := by
  rw [fOrig_eq_virtualPoly, honestRows pub B u (preOf ch) b]
  have hl : lanesComp (preOf ch 2) (laneOf u pub (preOf ch 0) (preOf ch 1) B) b = 0 := by
    unfold lanesComp
    exact Finset.sum_eq_zero (fun i _ => by
      rw [show laneOf u pub (preOf ch 0) (preOf ch 1) B i b = 0 from h1 i b, mul_zero])
  rw [hl, mul_zero, zero_add]
  rfl

/-- DESIGN-ii-prime §1.5: with the lanes zero and both helper sums zero, the
Boolean sum of the original terminal vanishes (honestRows, lane_h1_sum,
lane_inactive_sum). -/
theorem bsum_fOrig_zero_of (pub : Public K) (B : PackBasis F) (ch : Challenges K) (u : Trace K)
    (h1 : ∀ i b, laneOf u pub (ch.sem 0) (ch.sem 1) B i b = 0)
    (h2 : ∑ r, u 26 r = 0) (h3 : ∑ r ∈ copyInactiveRows, u 26 r = 0) :
    bsumB 10 (fun b => fOrig pub B ch u (ofBool b)) = 0 := by
  have hs : (fun b => fOrig pub B ch u (ofBool b)) = fun b => ch.sem 14 * (ch.sem 13 * u 26 (rowOf b) +
      ch.sem 13 ^ 2 * ((1 - copyActiveLiteral (copySelectors (rowSel (rowOf b)))) *
        u 26 (rowOf b))) := funext (fOrig_ofBool pub B ch u h1)
  rw [hs, bsumB_smul, bsumB_add, bsumB_smul, bsumB_smul, lane_h1_sum, lane_inactive_sum, h2, h3]
  simp only [mul_zero, add_zero]

theorem bsum_fOrig_zero (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (hv : HonestValid pub B t ch) :
    bsumB 10 (fun b => fOrig pub B ch (PayloadSplit.actual pub B t ch 0) (ofBool b)) = 0 :=
  bsum_fOrig_zero_of pub B ch _ hv.1 hv.2.1 hv.2.2

/-- DESIGN-ii-prime §1.5: ι vanishes on `cTilde` of a valid instance. -/
theorem iota_cTilde_zero (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (hv : HonestValid x.1 B (h.build w) ch) :
    iota (cTilde (Bat := Bat) h B x w ch) = 0 :=
  (iota_cTilde h B x w ch).trans (bsum_fOrig_zero x.1 B (h.build w) ch hv)

/-! ### The inactive sum -/

theorem dot_indicator (v : Fin 1024 → K) :
    dotLinear (AspisR0.Opening.indicator copyInactiveRows) v = ∑ r ∈ copyInactiveRows, v r := by
  unfold dotLinear
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply]
  have hi (i : Fin 1024) :
      (AspisR0.Opening.indicator copyInactiveRows i : K) • v i =
      if i ∈ copyInactiveRows then v i else 0 := by
    unfold AspisR0.Opening.indicator
    by_cases hm : i ∈ copyInactiveRows
    · simp only [hm, ↓reduceIte, one_smul]
    · simp only [hm, ↓reduceIte, zero_smul]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_ite_mem, Finset.univ_inter]

/-- If every lane of `τ` sums to zero over the inactive rows, so does `L τ`. -/
theorem inactive_L_zero (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K)
    (τ : Trace K) (hτ : ∀ l, ∑ r ∈ copyInactiveRows, τ l r = 0) :
    PayloadSplit.L (Bat := Bat) π B ch τ .inactiveSum = 0 := by
  rw [SilentReduction.L_inactiveSum, SilentReduction.linearPayload_inactiveSum]
  exact Finset.sum_eq_zero (fun l _ => by rw [dot_indicator, hτ l, mul_zero])

/-- Each semantic column of `applyEligible` is balanced over the inactive rows. -/
theorem applyEligible_inactive_sum (t : Trace K) (e : EligibleNoise K F) (l : Fin 29)
    (hl : l.val < 16) : ∑ r ∈ copyInactiveRows, applyEligible t e l r = 0 := by
  simp only [applyEligible, hl, ↓reduceIte]
  unfold balance
  exact SilentReduction.balance_sum_generic copyInactiveRows 1023 _ _ inactive_1023
    (fun s => t l s + semanticNoise (Sum.elim e 0) l s)

/-- Every lane of the eligible-noise trace is balanced over the inactive rows. -/
theorem eligible_inactive_sum (e : EligibleNoise K F) (l : Fin 29) :
    ∑ r ∈ copyInactiveRows, JointTrace.eligibleLinear e l r = 0 := by
  by_cases hl : l.val < 16
  · simp only [JointTrace.eligibleLinear_apply, hl, ↓reduceIte]
    unfold balance
    exact SilentReduction.balance_sum_generic copyInactiveRows 1023 _ _ inactive_1023
      (fun s => semanticNoise (Sum.elim e 0) l s)
  · simp only [JointTrace.eligibleLinear_apply, hl, ↓reduceIte, Finset.sum_const_zero]

/-- Every lane of the tape trace is balanced over the inactive rows. -/
theorem tape_inactive_sum (B : PackBasis F) (t : T K F) (l : Fin 29) :
    ∑ r ∈ copyInactiveRows, JointTrace.tapeLinear B t l r = 0 := by
  have he (r : Fin 1024) : JointTrace.tapeLinear B t l r =
      JointTrace.eligibleLinear t.2.2 l r + traceLinear B (aff t) l r := rfl
  rw [Finset.sum_congr rfl (fun r _ => he r), Finset.sum_add_distrib, eligible_inactive_sum,
    SilentReduction.traceLinear_inactive_sum, add_zero]

/-- DESIGN-ii-prime §1.4 (O2): `.inactiveSum` vanishes on the whole tape image. -/
theorem inactive_A (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F) (ch : Challenges K) (t : T K F) :
    A (Bat := Bat) π B ch t .inactiveSum = 0 := by
  have hA : A (Bat := Bat) π B ch t = PayloadSplit.L π B ch (JointTrace.tapeLinear B t) := rfl
  rw [hA]
  exact inactive_L_zero (Bat := Bat) π B ch (JointTrace.tapeLinear B t) (tape_inactive_sum B t)

/-- Every lane other than H1 of the payload trace is balanced over the inactive rows. -/
theorem actual_inactive_sum (pub : Public K) (B : PackBasis F) (t : Trace K) (ch : Challenges K)
    (l : Fin 29) (hl : l.val ≠ 26) :
    ∑ r ∈ copyInactiveRows, PayloadSplit.actual pub B t ch 0 l r = 0 := by
  have he : PayloadSplit.actual pub B t ch 0 =
      traceBase (prepare pub (applyEligible t (0 : T K F).2.2) ch) + traceLinear B (aff (0 : T K F)) :=
    applyAff_eq_base_add B (prepare pub (applyEligible t (0 : T K F).2.2) ch) (aff (0 : T K F))
  rw [he]
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, SilentReduction.traceLinear_inactive_sum, add_zero]
  by_cases h16 : l.val < 16
  · have hb (r : Fin 1024) : traceBase (prepare pub (applyEligible t (0 : T K F).2.2) ch) l r =
        applyEligible t (0 : T K F).2.2 l r := by
      simp only [traceBase, prepare, h16, hl, true_or, ↓reduceIte]
    rw [Finset.sum_congr rfl (fun r _ => hb r)]
    exact applyEligible_inactive_sum t _ l h16
  · have hb (r : Fin 1024) : traceBase (prepare pub (applyEligible t (0 : T K F).2.2) ch) l r = 0 := by
      simp only [traceBase, h16, hl, or_self, ↓reduceIte]
    rw [Finset.sum_congr rfl (fun r _ => hb r), Finset.sum_const_zero]

theorem inactive_c (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    JointView.c (Bat := Bat) h B x w ch .inactiveSum = ch.opening 0 ^ (26 : Fin 29).val *
      ∑ r ∈ copyInactiveRows, PayloadSplit.actual x.1 B (h.build w) ch 0 26 r := by
  have hO : PayloadSplit.O (Bat := Bat) x.1 B ch
      (PayloadSplit.actual x.1 B (h.build w) ch 0) .inactiveSum = 0 := rfl
  rw [c_eq, Pi.add_apply, hO, add_zero, SilentReduction.L_inactiveSum,
    SilentReduction.linearPayload_inactiveSum, Finset.sum_eq_single (26 : Fin 29)]
  · rw [dot_indicator]
  · intro l _ hl
    rw [dot_indicator, actual_inactive_sum _ _ _ _ l (fun he => hl (Fin.ext he)), mul_zero]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-- DESIGN-ii-prime §1.4 (O2) on `cTilde`. -/
theorem inactive_cTilde (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) :
    cTilde (Bat := Bat) h B x w ch .inactiveSum = ch.opening 0 ^ (26 : Fin 29).val *
      ∑ r ∈ copyInactiveRows, PayloadSplit.actual x.1 B (h.build w) ch 0 26 r := by
  have hd : (dir : Payload K Bat) .inactiveSum = 0 := rfl
  unfold cTilde
  rw [Pi.sub_apply, Pi.smul_apply, hd, smul_zero, sub_zero]
  exact inactive_c h B x w ch

theorem inactive_cTilde_zero (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w : h.Instance) (ch : Challenges K) (hv : HonestValid x.1 B (h.build w) ch) :
    cTilde (Bat := Bat) h B x w ch .inactiveSum = 0 := by
  rw [inactive_cTilde, hv.2.2, mul_zero]

/-- (R2)/(R3) of DESIGN-ii-prime §2.3 for the (★) difference of two valid witnesses. -/
theorem iota_inactive_diff_zero (h : HonestProver K) (B : PackBasis F)
    (x : Statement K CommitHandle) (w w' : h.Instance) (ch : Challenges K)
    (hv : HonestValid x.1 B (h.build w) ch) (hv' : HonestValid x.1 B (h.build w') ch) :
    iota (cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch) = 0 ∧
      (cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch : Payload K Bat) .inactiveSum = 0 := by
  refine ⟨?_, ?_⟩
  · rw [map_sub, iota_cTilde_zero h B x w ch hv, iota_cTilde_zero h B x w' ch hv', sub_zero]
  · rw [Pi.sub_apply, inactive_cTilde_zero h B x w ch hv, inactive_cTilde_zero h B x w' ch hv',
      sub_zero]

/-! ### The obstruction (DESIGN-ii-prime §1.4) -/

/-- Unequal ι-values are never related by the tape image: clause (ii′) without
a validity premise fails for any prover with two such instances. -/
theorem not_iiPrime_witness (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w w' : h.Instance) (ch : Challenges K)
    (hne : iota (cTilde (Bat := Bat) h B x w ch) ≠ iota (cTilde (Bat := Bat) h B x w' ch)) :
    cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch ∉ LinearMap.range (A h.transport B ch) := by
  rintro ⟨t, ht⟩
  apply hne
  have h0 := iota_A (Bat := Bat) h.transport B ch t
  rw [ht, map_sub] at h0
  exact sub_eq_zero.mp h0

/-- The same for unequal inactive sums. -/
theorem not_iiPrime_inactive (h : HonestProver K) (B : PackBasis F) (x : Statement K CommitHandle)
    (w w' : h.Instance) (ch : Challenges K)
    (hne : cTilde (Bat := Bat) h B x w ch .inactiveSum ≠ cTilde (Bat := Bat) h B x w' ch .inactiveSum) :
    cTilde (Bat := Bat) h B x w ch - cTilde h B x w' ch ∉ LinearMap.range (A h.transport B ch) := by
  rintro ⟨t, ht⟩
  apply hne
  have h0 := inactive_A (Bat := Bat) h.transport B ch t
  rw [ht, Pi.sub_apply] at h0
  exact sub_eq_zero.mp h0

#print axioms inactive_1023
#print axioms HonestValid
#print axioms ValidOn
#print axioms IIPrimeValid
#print axioms ZkStatement.HonestProver.restrict
#print axioms sRem_restrict
#print axioms cTilde_restrict
#print axioms inLanguage_restrict
#print axioms maskImageOn_restrict_iff
#print axioms maskImageOn_restrict_of
#print axioms hvzk_on_restrict
#print axioms zkfs_restrict_abort
#print axioms zkfs_restrict_abort_terms
#print axioms iota_L
#print axioms iota_A
#print axioms iota_originalRounds
#print axioms iota_dir
#print axioms c_eq
#print axioms iota_c
#print axioms iota_cTilde
#print axioms fOrig_eq_virtualPoly
#print axioms fOrig_ofBool
#print axioms bsum_fOrig_zero_of
#print axioms bsum_fOrig_zero
#print axioms iota_cTilde_zero
#print axioms dot_indicator
#print axioms inactive_L_zero
#print axioms applyEligible_inactive_sum
#print axioms eligible_inactive_sum
#print axioms tape_inactive_sum
#print axioms inactive_A
#print axioms actual_inactive_sum
#print axioms inactive_c
#print axioms inactive_cTilde
#print axioms inactive_cTilde_zero
#print axioms iota_inactive_diff_zero
#print axioms not_iiPrime_witness
#print axioms not_iiPrime_inactive
end R0Z.HonestValid
