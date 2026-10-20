# Scan freshness — 2026-10-21

Branch `codex/cx-priv-history3-20261021`, base `55c62085d`.

## Stage 1: actual input trace

`QueryScanFreshInputs.real_scan_addresses` proves the exact real-side inputs,
not only an address grammar analogy. For block zero the state is the answer
of `absQ`. For block n+1 it is the answer of `qa n`. Squeeze reads append
byte 1; advance reads append byte 2. No separate prover secret, salt or block
counter occurs in either input. Both members of a pair share their state;
the second member has a different suffix, not a new independent state.

`FreshFailure` defines the scan-specific event operationally, at the partial
answer vector immediately before each query. It includes the initial public
digest and every earlier honest scheduled read, including previous attempts.
It excludes the post-proof observer. `off_fresh_failure` gives precisely the
freshness consequence, without asserting a probability law.

Focused env J 9832: exit 0; wall 2.14 s; peak RSS 4,051,128 KiB; swaps 0.
Four theorem audits use only subsets of propext, Classical.choice, Quot.sound.
9830/9831 retain local elaboration failures, followed by changed source.
Full source revision, SHA256, dependency fingerprint, errors, axioms and raw
launcher/time output are in `history-fresh-attempts-9800-9999.jsonl`.

Further stages and endpoint status will be recorded below. Existing modules
are unchanged. Build runner is the assigned env J run-joint.sh, -M7000,
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0; reservation 24 GiB + this 7 GiB.

## Stage 2: proved unconditional real parser bound

`QueryScanRealLazyBound.real_bad_union_mass` proves, on the exact real
randomness carrier (uniform table times independent attempt secrets),

    mass (some real attempt's selected parser fails)
      ≤ (M²+M)/2^255 + N * scanProbability,
    M = N * n1 W Pr.

This is independent progress beyond the previous two runs: it is an actual
unconditional real-model parser law, not a fixed-state subrun or a conditional
law on every history. It uses `meanR_P`, `run_eq_lazy`, `pair_all`, `pf_pub`,
the LE independent-word law and the selected-stop bridge. The honest-program
collision event is charged once outside the union over attempts. It includes
no observer calls. It is broader than E_fresh and therefore does not alone
prove the requested sharper scan-only law. The source event is fixed by the
parser; it is not an arbitrary realBad predicate.

Env J 9839: exit 0; wall 3.64 s; peak RSS 4,068,172 KiB; swaps 0; six
standard-axiom audits. 9833–9838 preserve elaboration failures; changes factored
coordinate projection and finite-instance transport symbolically. No limit
was raised and no unchanged source was rerun. Only this new module's drafts
and objects were replaced, with branch-specific host snapshots.

## Stage 3: a real-law-free endpoint and actual E_fresh

`PrivacyR1FinalProtocolHistoryReal.privacy_R1_protocol_history_real` compiles
with `real_model_history_law` deleted, realBad fixed to the actual real
selected parser failure, and the same execution-only joins. It proves ZK
with error `modelError + 16/2^486 + (M²+M)/2^255`, its corresponding numerical
upper bound, and strict error `< 2^-100`. The honest collision charge appears
once across all eight real attempts. No new probability premise replaces the
deleted law. Source joins still preserve the complete observation; their
event identification is now fixed. This is a conservative endpoint, not yet
the requested sharp scan-only endpoint.

`QueryScanRealFreshMass.real_fresh_mass` also bounds the actual E_fresh by
`(M²+M)/2^255`. It proves that addresses computed at issue time equal their
final causal-vector addresses, then transports the scan-specific reuse event
through the real lazy coupling. It does not equate E_fresh to the broader
honest collision event or charge observer repeats.

Final focused receipts so far: join/numerics 9842, exit 0, 2.69 s,
4,063,136 KiB, zero swaps, three standard-axiom audits; actual E_fresh 9847,
exit 0, 2.52 s, 4,052,056 KiB, zero swaps, three audits; endpoint 9848,
exit 0, 9.69 s, 4,077,540 KiB, zero swaps, one standard-axiom audit.
9840/9841/9843–9846 retain errors followed by source changes. One endpoint
arithmetic warning concerns tactic preprocessing of an exponent; the proof
succeeds without evaluating any recurrence or large finite universe.

## Stage 4: actual entropy, scan union, fresh words, and final endpoint

The final endpoint supersedes the conservative-only endpoint above. Its
internal theorem is retained as `privacy_R1_protocol_history_real_of_lazy_budget`.

### Entropy and earlier-entry pairs

`QueryScanRealEntropy.real_state_min_entropy` proves on the actual real
carrier, for every attempt, block and fixed 256-bit value z,

    mass (real scan state = z) ≤ 2^-190.

This is a deliberately conservative marginal min-entropy theorem, not a
claim of entropy after revealing that same state. Off the honest lazy
collision event the state is exactly its independent predecessor coordinate;
that coordinate has 256 bits. The exceptional mass is ≤ 2^-204 under the
existing M≤2^25 binary read-count envelope. Unioning its point mass gives
≤2^-203, hence the stated k=190. No extra entropy hypothesis is introduced.
The source of state randomness is the oracle answer of absQ or the preceding
advance read, not an invented salt/counter. The second read of a pair uses
its sibling's already-used state with a distinct suffix.

Marginal min-entropy alone would not justify comparing correlated addresses.
`prior_hit_mass` therefore separately proves every actual scan/earlier-entry
pair has mass ≤2^-190 using the real/lazy coupling, including upstream
collisions. It conservatively uses the stronger 204-bit exception envelope.
`fresh_iff_prior_hit` identifies **exactly E_fresh**, then `real_fresh_linear`
unions the 128 scan calls (8 attempts × 8 blocks × squeeze/advance) against
at most q earlier entries, including the initial digest:

    mass E_fresh ≤ 128 * q / 2^190,   M+1 ≤ q.

This is a valid, deliberately loose per-pair bound. It does not claim a
tight 256-bit local conditional law or deduce a correlated guessing law
from marginal entropy. No whole-run adversary-repeat event is used.
In the constructed real game the observer runs only after the honest
attempts; its later queries cannot already be in the table at scan issue.
Taking q=M+1 bounds the entire earlier-entry universe. Any larger total-query
envelope preserves the bound by monotonicity.

### Fresh-word law

`QueryScanFreshProgram` introduces a marked-read interpreter over the
existing `MemoizedProgramLaw.Program`, not a replacement oracle. Unmarked
reads can repeat arbitrarily. Its `fresh_oracle_bound` proves that the mass
of a nonnegative marked-word test, intersected with freshness of its marked
reads, is at most its independent-word mean. Cached marked reads contribute
zero to this subevent; fresh marked reads expose one independent coordinate.
The proof is structural induction plus the retained exact memoized-oracle
law. It does not condition on all future revealed answers.

`QueryScanFreshWords.queries_eval` identifies the compiled squeeze/advance
fragment with the retained `queryState`/`queryBlocks` recurrence, symbolically
in the number of blocks. `fresh_program_scan_le` gives scanProbability for
any eight marked calls, including arbitrary unmarked history. More directly,
`fresh_query_fragment_le` gives the exact eight-block fragment the selected
first-stop LE parser bound from **any consistent prior memo table and any
starting state**. This is the fresh-history subevent law; it does not assert
the false bound on every unrestricted shared-ROM history.

The endpoint does not require a further full-RealRand projection of this
fragment theorem: its independent real parser union theorem already provides
a conservative valid route. In particular, it does **not** infer that
¬E_fresh implies the whole honest read program has distinct inputs.

### Final numerical and endpoint result

Write M=8*n1 and q=M+1. The final endpoint has error

    modelError + 16/2^486 + freshBudget q,
    freshBudget q = 128*q/2^190.

It deletes `real_model_history_law` and arbitrary realBad, fixes the source
real join to the actual real parser failures, retains the execution-only
ideal join, and adds no replacement probability/entropy premise. The same
freshness allowance dominates the conservative internal lazy-collision
budget. **That is an inequality of numerical budgets, not equality of events.**
Consequently it is added once, outside the union over all real attempts.
The internal proof excludes more honest histories than E_fresh, while the
published numerical allowance is a proved bound for E_fresh itself as well.

`fresh_budget_mono`, `fresh_budget_pow65`, `fresh_budget_small` and
`fresh_total_lt_target` prove symbolically, for every q≤2^65,

    freshBudget q ≤ freshBudget (2^65) = 2^-118 ≤ 2^-109,
    2^-109 + 2^-137 + 2^-454 + freshBudget q < 2^-100.

The endpoint derives M≤2^25 and q=M+1≤2^65 from the retained commitment cell
and block budgets. It does not assume this count as a source probability law.
The theorem exports both the new explicit error bound and strict <2^-100.

Final focused receipts: marked interpreter 9853, exit 0, 2.36 s,
4,055,416 KiB, five audits; real entropy 9854, exit 0, 3.79 s,
4,070,112 KiB, four audits; scan/earlier-entry union 9856, exit 0, 3.25 s,
4,069,748 KiB, four audits; final numerics 9860, exit 0, 2.18 s,
4,058,772 KiB, six audits; exact scan fragment 9862, exit 0, 2.29 s,
4,060,060 KiB, four audits; final endpoint 9863, exit 0, 8.61 s,
4,079,124 KiB, two audits. All swaps zero, all axioms standard or subsets.
Earlier changed-source failures are retained in the JSONL evidence. The
final endpoint uses a symbolic arithmetic identity so there is no large
exponent preprocessing warning in its final receipt.

## Exact signature diff

```diff
--- PrivacyR1FinalProtocolHistory
+++ PrivacyR1FinalProtocolHistoryReal
@@ -1,4 +1,4 @@
-theorem privacy_R1_protocol_history
+theorem privacy_R1_protocol_history_real
     (seed : R1ProverP K CommitHandle Aux F
       (wire base ((base.pubBytes x).length) h B outputs x).toWire)
     (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
@@ -25,19 +25,17 @@
     [Fintype source.IdealRand] [Nonempty source.IdealRand]
     (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
       List (List UInt8 × OracleAnswer) → OProg)
-    (realBad : source.Adversary → h.Instance → Fin 8 → (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).RealRand → Prop)
-    (real_model_history_law : ∀ adv w, h.public w = x.1 →
-      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
     (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
       h.public w = x.1 → ModelExecutionJoin
         (realTest h B outputs source adv x w)
         (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
-          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (realBad adv w))
+          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
     (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
       (idealTestS source adv x (simE h.transport B outputs x))
       (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
         (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
     ZK_FSS h B outputs source x (simE h.transport B outputs x)
-      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
-    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
-      1 / 2^109 + 1 / 2^137 + 1 / 2^454+      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
+    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
+      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
+    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```

## Before, verbatim

```lean
theorem privacy_R1_protocol_history
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (realBad : source.Adversary → h.Instance → Fin 8 → (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).RealRand → Prop)
    (real_model_history_law : ∀ adv w, h.public w = x.1 →
      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (realBad adv w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454
```

## After, verbatim

```lean
theorem privacy_R1_protocol_history_real
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```

## Final evidence and retained source boundary

`python3 r1p-final/audit-history-fresh.py` passes: 34 new assigned attempts
9830–9863, ten final modules, 41 theorem audits, no duplicate source/dependency
retries, final source and dependency-object SHA256 pins, compiled object
SHA256/size (no binaries), zero swaps, generator `--check`, and verbatim
signature checks. `history-fresh-final-audit.json` records all final targets,
exit, wall, peak RSS, swap, source revision/hash, dependencies, object pins and
axioms. `history-fresh-attempts-9800-9999.jsonl` retains every raw output,
failed elaboration, launcher reservation and full timing record. Audited
proof-source revision: `75e1fe6b9c233d3b2cb759ed87bc7003b0660b11`.

All 302 pre-existing PRIVACY Lean modules match base `55c62085d`. In
particular, PrivacyR1Final, PrivacyR1FinalProtocol and PrivacyR1FinalProtocolHistory
are unchanged; only new modules are added. BuilderSource, SourceIdentification,
builder_refinement_D46_D51 and Rust harnesses are untouched. Each host update
was to this branch's new source/object, with prior drafts snapshotted under
`snapshots/codex-cx-priv-history3-20261021/<attempt>`.

No frozen certificate/manifest or runtime artifact changed. The final focused
endpoint bridge is green; no unchanged package-wide/certificate replay,
Rust suite, SBF rebuild or frozen ELF gate was repeated. All Lean jobs used
the assigned env J launcher, -M7000, MemoryHigh=5G, MemoryMax=7G and
MemorySwapMax=0, with the launcher's aggregate reservation check.

The retained obligations are the explicit builder/packing/tape/batch/log and
source real/ideal execution joins in the quoted final statement. They remain
source correspondence work; no model proof here asserts Rust extraction or
whole-observation agreement for an arbitrary source. The real model mass law
is no longer an endpoint premise. The probability proof is conservative and
does not claim a tight 256-bit conditional state law. No wallet/key operation,
push, merge or edit outside this worktree was performed.
