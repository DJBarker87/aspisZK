/-
MAT_MultiAttempt: repeated, separately submitted spend attempts against one
oracle (stand-in level).

Target not yet established.  Core Lean plus RSL_/TCK_/TAS_/TFM_/EVB_/TAS_TopB
only.  No sorry, no axiom declaration, no Root0 hypothesis, no hash-injectivity
premise, no Realizes premise.

What this file proves.
  * `union_charge` (generic): for any expectation `Ex` with `mono`/`add`
    (TASB.Expect), events `F i` dominated by losses `l i` with `Ex.E (l i) ≤ T i`
    give `Ex.E 1_{∃ i < k, F i} ≤ Σ_{i<k} T i`.  No conditioning, no
    independence: only the unconditional marginal bound of each attempt is used.
  * `campaign_charge`: the per-attempt theorem `RSL.TASB.deployed_charge`
    applied once per attempt i to the REDUCTION adversary `fxOf i` (which runs
    the whole campaign prefix and outputs attempt i's pair), each with its own
    world map `wOf i`, then `union_charge`.  Conclusion: the probability, over
    the one shared oracle H, that SOME attempt i < k is a successful actual run
    whose OutcomeRec fails is at most Σ_{i<k} T i, where T i is the budget of
    attempt i's reduction adversary (host: total (Q0+Q1) at `fxOf i`).  A
    second conclusion keeps the extractor-failure mass: the sum over attempts of
    the per-attempt loss `max r_i 1_{fail_i}` has mean ≤ Σ T i.
  * `campaign_numeric`: if every attempt's reduction budget Q i ≤ Qbar ≤
    maxQueries, then Σ_{i<k} total (Q i) ≤ k·(Qbar+1)·eps, using only the host
    `F3U_Range.per_attempt` (a hypothesis here, eps = 2^-100).
  * `reduction_cost_le` + `campaign_bound`: with the reduction cost
    Q i ≤ c·(qAdv i + V·i), cumulative adversary queries qAdv i ≤ qTot and
    V = per-attempt verifier envelope (2322), every Q i ≤ c·(qTot + V·(k-1)),
    giving  Pr[some attempt forges] ≤ k·(c·(qTot + V·(k-1)) + 1)·2^-100.
    For the current host adversary type c = 2 (MAT_REPORT.md section 3).

Query counting.  Attempt i is charged at its reduction adversary's issued-call
count, i.e. CUMULATIVELY: every adversary query before attempt i's pair is
fixed (all earlier attempts included), plus a re-issue of every earlier
attempt's verifier digest calls, plus (c = 2) the second phase's recomputation
of the first phase.  It is NOT charged at its fresh queries q_i with
Σ q_i ≤ Q_total: that would be a per-attempt bound conditioned on the history,
which `deployed_charge` does not state and which fails in general (an earlier
attempt's queries may have found the transcript start that attempt i reuses).

Host obligations NOT discharged here (each is a field or hypothesis below and
is named in MAT_REPORT.md section 4):
  (H-MA1) construction of the reduction adversary a_i : SCE_Experiment.Adversary
          from a campaign adversary, with (eval H a_i.first).2 and
          (eval H (a_i.second …)).2 equal to attempt i's submitted inputs;
  (H-MA2) its issued-call bound, `cost` below;
  (H-MA3) the campaign environment condition: whatever the campaign adversary
          observes between attempts is a function of H and of oracle-free data
          fixed before H (so it can be hard-wired into a_i or recomputed with
          charged queries).
-/
import TAS_TopB
set_option autoImplicit false

namespace RSL.MAT
open RSL.TAS RSL.TFM RSL.EVB RSL.TASB
open TX2_241 (V2Lib Dom064)
open TX1_345 (S1Lib)

/-! ## 1. Finite sums over attempts and the union bound -/

/-- `sumTo f k = f 0 + … + f (k-1)`. -/
def sumTo (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem addLe {a b c d : Rat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Rat.le_trans ((Rat.add_le_add_right (c := c)).mpr h1) ((Rat.add_le_add_left (c := b)).mpr h2)

theorem leMaxR (a b : Rat) : b ≤ max a b := by
  rw [Rat.max_def]; split
  · exact Rat.le_refl
  · rename_i h; exact Rat.le_of_lt (Rat.not_le.mp h)

theorem ind_nonneg (p : Prop) : 0 ≤ ind p := by
  classical
  rw [ind_def]; split
  · decide
  · exact Rat.le_refl

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  classical
  rw [ind_def]; split
  · exact Rat.le_refl
  · decide

theorem sumTo_le {f g : Nat → Rat} : ∀ n, (∀ i, i < n → f i ≤ g i) → sumTo f n ≤ sumTo g n
  | 0, _ => Rat.le_refl
  | n + 1, h => addLe (sumTo_le n (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

theorem sumTo_nonneg {f : Nat → Rat} : ∀ n, (∀ i, 0 ≤ f i) → 0 ≤ sumTo f n
  | 0, _ => Rat.le_refl
  | n + 1, h => by
      have := addLe (sumTo_nonneg n h) (h n)
      rwa [Rat.add_zero] at this

theorem expect_zero {Ω : Type} (Ex : Expect Ω) : Ex.E (fun _ => 0) = 0 := by
  have h := Ex.add (fun _ => (0 : Rat)) (fun _ => 0)
  simp only [Rat.add_zero] at h
  have h' : Ex.E (fun _ => 0) + 0 = Ex.E (fun _ => 0) + Ex.E (fun _ => 0) := by
    rw [Rat.add_zero]; exact h
  exact (Rat.add_left_cancel _ h').symm

/-- Linearity of the expectation over finitely many attempts. -/
theorem expect_sumTo {Ω : Type} (Ex : Expect Ω) (f : Nat → Ω → Rat) :
    ∀ n, Ex.E (fun H => sumTo (fun i => f i H) n) = sumTo (fun i => Ex.E (f i)) n
  | 0 => expect_zero Ex
  | n + 1 => by
      show Ex.E (fun H => sumTo (fun i => f i H) n + f n H) = _
      rw [Ex.add (fun H => sumTo (fun i => f i H) n) (f n), expect_sumTo Ex f n]
      rfl

/-- Pointwise union bound: the indicator of "some attempt i < n" is at most
the sum of the per-attempt indicators. -/
theorem ind_exists_le_sum (P : Nat → Prop) :
    ∀ n, ind (∃ i, i < n ∧ P i) ≤ sumTo (fun i => ind (P i)) n
  | 0 => by
      classical
      have : ¬ ∃ i, i < 0 ∧ P i := fun ⟨_, h, _⟩ => Nat.not_lt_zero _ h
      rw [ind_def, if_neg this]; exact Rat.le_refl
  | n + 1 => by
      classical
      show _ ≤ sumTo (fun i => ind (P i)) n + ind (P n)
      by_cases hp : P n
      · have h1 : ind (∃ i, i < n + 1 ∧ P i) ≤ 0 + 1 := by
          rw [Rat.zero_add]; exact ind_le_one _
        have h2 : (1 : Rat) ≤ ind (P n) := by rw [ind_def, if_pos hp]; exact Rat.le_refl
        exact Rat.le_trans h1 (addLe (sumTo_nonneg n (fun i => ind_nonneg _)) h2)
      · have iff : (∃ i, i < n + 1 ∧ P i) ↔ (∃ i, i < n ∧ P i) := by
          constructor
          · rintro ⟨i, hi, pi⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
            · exact ⟨i, h, pi⟩
            · subst h; exact absurd pi hp
          · rintro ⟨i, hi, pi⟩; exact ⟨i, Nat.lt_succ_of_lt hi, pi⟩
        have h0 : ind (P n) = 0 := by rw [ind_def, if_neg hp]
        rw [h0, Rat.add_zero, propext iff]
        exact ind_exists_le_sum P n

/-- Generic union bound over attempts, under the TASB expectation.  Uses only
the unconditional bound of each attempt; no independence across attempts and
no conditioning on the history is assumed or needed. -/
theorem union_charge {Ω : Type} (Ex : Expect Ω) (k : Nat) (F : Nat → Ω → Prop)
    (l : Nat → Ω → Rat) (T : Nat → Rat)
    (dom : ∀ i H, ind (F i H) ≤ l i H)
    (each : ∀ i, i < k → Ex.E (l i) ≤ T i) :
    Ex.E (fun H => ind (∃ i, i < k ∧ F i H)) ≤ sumTo T k := by
  have pw : ∀ H, ind (∃ i, i < k ∧ F i H) ≤ sumTo (fun i => l i H) k := fun H =>
    Rat.le_trans (ind_exists_le_sum (fun i => F i H) k)
      (sumTo_le k (fun i _ => dom i H))
  have h := Ex.mono _ _ pw
  rw [expect_sumTo Ex l k] at h
  exact Rat.le_trans h (sumTo_le k each)

/-! ## 2. The campaign at the split-B instantiation -/

variable {S : Sig} {R : RecSig S}

/-- Attempt failure at world H: the deployed pair of the reduction adversary
`fx` is a successful actual run and its Outcome (bad := E_rec) fails.  This is
exactly the event inside `deployed_charge`. -/
def Forged {L : PoolLib} {V0 : V2Lib} {VL : VLib} (I : Impl L V0 VL) (hb : HeadlineB S R)
    (X : ExecB S R) (fx : X.Fixed) (w : X.World) (H : X.Oracle) : Prop :=
  Runs S I (ctxB X fx w H) ∧
    ¬ hb.OutcomeRec (ctxB X fx w H) (S.model1 (ctxB X fx w H)) (S.model2 (ctxB X fx w H))

/-- Campaign bound.  k attempts against ONE oracle H (one `X`, one `Ex`).
Attempt i is the per-attempt experiment of `deployed_charge` at the reduction
adversary `fxOf i` (host: the program that simulates the campaign through
attempt i, H-MA1) and the world map `wOf i` (chain state of attempt i, any
function of H, so state left by earlier attempts is covered).  Each attempt's
inputs `r i`, `m i`, `budget i` are exactly the per-attempt host inputs at
`fxOf i`.  Conclusions:
  (1) Pr_H[∃ i < k, attempt i forged] ≤ Σ_{i<k} T i;
  (2) E_H[Σ_{i<k} max (r i H) 1_{attempt i forged}] ≤ Σ_{i<k} T i
      (extractor-failure mass kept, E_rec charged once per attempt). -/
theorem campaign_charge (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (Ex : Expect X.Oracle) (k : Nat)
    (fxOf : Nat → X.Fixed) (wOf : Nat → X.Oracle → X.World)
    (queries : ∀ i, i < k → X.QueriesF (fxOf i))
    (r m : Nat → X.Oracle → Rat) (T : Nat → Rat)
    (hm : ∀ i, i < k → ∀ H, 0 ≤ m i H)
    (each : ∀ i, i < k → ∀ H, r i H ≤ m i H + ind (X.ERec (fxOf i) H))
    (budget : ∀ i, i < k → Ex.E (m i) + Ex.E (fun H => ind (X.ERec (fxOf i) H)) ≤ T i) :
    Ex.E (fun H => ind (∃ i, i < k ∧ Forged I hb X (fxOf i) (wOf i H) H)) ≤ sumTo T k ∧
      Ex.E (fun H => sumTo (fun i => max (r i H) (ind (Forged I hb X (fxOf i) (wOf i H) H))) k)
        ≤ sumTo T k := by
  have per : ∀ i, i < k →
      Ex.E (fun H => max (r i H) (ind (Forged I hb X (fxOf i) (wOf i H) H))) ≤ T i :=
    fun i hi => deployed_charge L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo nmn
      g1a rs hb nmfB r0 a1 a2 a3 a4 a5 er X Ex (fxOf i) (wOf i) (queries i hi)
      (r i) (m i) (T i) (hm i hi) (each i hi) (budget i hi)
  refine ⟨union_charge Ex k (fun i H => Forged I hb X (fxOf i) (wOf i H) H)
    (fun i H => max (r i H) (ind (Forged I hb X (fxOf i) (wOf i H) H))) T
    (fun i H => leMaxR _ _) per, ?_⟩
  rw [expect_sumTo Ex (fun i H => max (r i H) (ind (Forged I hb X (fxOf i) (wOf i H) H))) k]
  exact sumTo_le k per

/-! ## 3. Numeric form and query accounting -/

theorem sumTo_const_le {f : Nat → Rat} (c : Rat) :
    ∀ n, (∀ i, i < n → f i ≤ c) → sumTo f n ≤ (n : Rat) * c
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
      have ih := sumTo_const_le c n (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have e : ((n + 1 : Nat) : Rat) * c = (n : Rat) * c + c := by
        rw [Rat.natCast_add, Rat.add_mul]; simp
      rw [e]
      exact addLe ih (h n (Nat.lt_succ_self n))

/-- Per-attempt numeric bound summed over the campaign.  `perAttempt` is the
host `F3U_Range.per_attempt` (total := F3T_Numeric.total, eps := 1/2^100,
maxQ := F3U_RangeEdges.maxQueries).  Every attempt is evaluated at its own
reduction budget `Q i`, all inside the valid range. -/
theorem campaign_numeric (total : Nat → Rat) (eps : Rat) (heps : 0 ≤ eps) (maxQ : Nat)
    (perAttempt : ∀ Q, Q ≤ maxQ → total Q ≤ ((Q : Rat) + 1) * eps)
    (k : Nat) (Q : Nat → Nat) (Qbar : Nat)
    (hQ : ∀ i, i < k → Q i ≤ Qbar) (hbar : Qbar ≤ maxQ) :
    sumTo (fun i => total (Q i)) k ≤ (k : Rat) * (((Qbar : Rat) + 1) * eps) := by
  apply sumTo_const_le
  intro i hi
  refine Rat.le_trans (perAttempt (Q i) (Nat.le_trans (hQ i hi) hbar)) ?_
  apply Rat.mul_le_mul_of_nonneg_right _ heps
  exact (Rat.add_le_add_right (c := 1)).mpr (Rat.natCast_le_natCast.mpr (hQ i hi))

/-- Reduction cost arithmetic.  `qAdv i`: the campaign adversary's own issued
queries up to the moment attempt i's pair is fixed (cumulative, includes all
earlier attempts); `V`: verifier digest calls per submitted attempt, which the
reduction adversary re-issues for the i earlier attempts; `c`: phase factor
(c = 2 when the second phase must recompute the first, as for the current
`SCE_Experiment.Adversary`, whose `second` receives no private state). -/
theorem reduction_cost_le (c V qTot k : Nat) (qAdv Q : Nat → Nat)
    (cost : ∀ i, i < k → Q i ≤ c * (qAdv i + V * i))
    (tot : ∀ i, i < k → qAdv i ≤ qTot) :
    ∀ i, i < k → Q i ≤ c * (qTot + V * (k - 1)) := by
  intro i hi
  refine Nat.le_trans (cost i hi) (Nat.mul_le_mul_left c (Nat.add_le_add (tot i hi) ?_))
  exact Nat.mul_le_mul_left V (by omega)

/-- Composed campaign bound at stand-in level: with every attempt's budget
`T i := total (Qof (fxOf i))` (host: `failureModel ≤ total (Q0+Q1)` at the
reduction adversary), the reduction cost `cost` (H-MA2) and the cumulative
adversary budget `qTot`, if `c·(qTot + V·(k-1)) ≤ maxQ` then
  Pr_H[∃ i < k, attempt i forged] ≤ k · (c·(qTot + V·(k-1)) + 1) · eps. -/
theorem campaign_bound (L : PoolLib) (D : DeployedIds) (V0 : V2Lib) (VL : VLib)
    (P : PreparedNew VL) (C : S1Lib VL) (I : Impl L V0 VL)
    (sp : Split S) (hl : Headline S) (a0 : A0_Digest S)
    (nmm : NMM_Roots L D V0 VL I) (nmx : NMX_Root L D V0 VL I) (nms : NMS_Roots L D V0 VL I)
    (nmv : NMV_Roots L D V0 VL P C I) (nmw : NMW_Roots L D V0 VL P C I)
    (nmt : NMT_Roots L V0 VL P C I) (nmp : NMP_Roots L V0 VL P I) (nmo : NMO_Root L V0 VL I)
    (nmn : NMN_Root L V0 VL I)
    (g1a : NNC_G1a S L V0 VL I) (rs : RecSelect S R) (hb : HeadlineB S R)
    (nmfB : NNC_NMFPrimeB S L D V0 VL P C I g1a R) (r0 : NNC_R0Rep S V0)
    (a1 : NND_A1 S VL P C) (a2 : NND_A2 S L D V0)
    (a3 : NNE_A3 S VL P C) (a4 : NNE_A4 S L D V0) (a5 : NNE_A5 S L V0 VL P C I)
    (er : NNE_EntryRep S L V0 VL I)
    (X : ExecB S R) (Ex : Expect X.Oracle) (k : Nat)
    (fxOf : Nat → X.Fixed) (wOf : Nat → X.Oracle → X.World)
    (queries : ∀ i, i < k → X.QueriesF (fxOf i))
    (r m : Nat → X.Oracle → Rat)
    (total : Nat → Rat) (eps : Rat) (heps : 0 ≤ eps) (maxQ : Nat)
    (perAttempt : ∀ Q, Q ≤ maxQ → total Q ≤ ((Q : Rat) + 1) * eps)
    (Qof : X.Fixed → Nat)
    (hm : ∀ i, i < k → ∀ H, 0 ≤ m i H)
    (each : ∀ i, i < k → ∀ H, r i H ≤ m i H + ind (X.ERec (fxOf i) H))
    (budget : ∀ i, i < k →
      Ex.E (m i) + Ex.E (fun H => ind (X.ERec (fxOf i) H)) ≤ total (Qof (fxOf i)))
    (c V qTot : Nat) (qAdv : Nat → Nat)
    (cost : ∀ i, i < k → Qof (fxOf i) ≤ c * (qAdv i + V * i))
    (tot : ∀ i, i < k → qAdv i ≤ qTot)
    (range : c * (qTot + V * (k - 1)) ≤ maxQ) :
    Ex.E (fun H => ind (∃ i, i < k ∧ Forged I hb X (fxOf i) (wOf i H) H)) ≤
      (k : Rat) * ((((c * (qTot + V * (k - 1)) : Nat) : Rat) + 1) * eps) := by
  have h := (campaign_charge L D V0 VL P C I sp hl a0 nmm nmx nms nmv nmw nmt nmp nmo nmn
    g1a rs hb nmfB r0 a1 a2 a3 a4 a5 er X Ex k fxOf wOf queries r m
    (fun i => total (Qof (fxOf i))) hm each budget).1
  exact Rat.le_trans h (campaign_numeric total eps heps maxQ perAttempt k
    (fun i => Qof (fxOf i)) _
    (reduction_cost_le c V qTot k qAdv (fun i => Qof (fxOf i)) cost tot) range)

#print axioms union_charge
#print axioms campaign_charge
#print axioms campaign_numeric
#print axioms reduction_cost_le
#print axioms campaign_bound

end RSL.MAT
