# Current status: 100-bit soundness and privacy (living page)

Last updated 2026-10-22 02:05 by the lead. This page is the single current
reference; dated notes keep the history.

## The contract

`design/SECURITY-CONTRACT-20261021.md`: **100-bit per-attempt soundness
without grinding credit.** (A) One attempt fails with probability ≤ 2^-100;
in particular the whole-experiment bound for an adversary making no queries
is ≤ 2^-100. (B) Repeated attempts are stated plainly as (starts)·B +
collision terms, keeping the Q-dependence. Everything below is in the
random-oracle model (SHA-256 as an ideal hash, premise P1).

## Soundness

**Headline: `OraclePortHeadlineFrozen2PerAttempt.final_soundness`**
(`lean/OraclePortHeadlineFrozen2PerAttempt.lean`).

    F ≤ (Q+34)·B + κ(Q+1161) + 2^-126 + 2^-454,   B = 15/2^109 ≈ 2^-105.09
    zero_queries:  F ≤ 2^-100

Here F is the failure probability of the deployed two-transaction flow
(stage 1, checkpoint, Pool stage 2), modelled exactly by `dV_frozen2` with
the frozen multiproof order and the six checkpoint reads. Q counts every oracle
query the adversary makes. The extractor cost is ≤ 4·scale³·(Q+2323)³.

| Premise | Meaning | Status | Owner |
|---|---|---|---|
| `hqueries` | the adversary makes at most Q queries | experiment parameter | — |
| `AcceptedRunJoin D rust` | on every accepted run, the frozen Rust's oracle log and outputs equal dV_frozen2's | open: split into per-cone joins (table below) | see below |
| `StoredCarrierBinding` | the runtime presents the same stored proof and accepted observation across both transactions | reduces to the same execution join plus the named runtime premises P2/P2′/P3/P4 (`STORED-CARRIER-20261021.md`) | lead |

Contract status: (A) and (B) are met **conditionally** on these premises.

Per-cone joins (`JOIN-SPLIT-DRAFT-20261021.md`, `CONE-AUDIT-20261021.md`):

| Cone | Status | Owner |
|---|---|---|
| S1, S3, S4, S5, S6, S9 | in progress | user's Codex |
| S2 (top-level verifier and adapter caller) | SDK metadata guard verified; stage-1 binding to first_decoded open (buffer operations being split) | user's Codex. **Critical path**: S7, S8, checkpoint and S10 wait on its caller interface |
| S7 | reference = dV_frozen2 stage, total; frozen caller adoption waits on S2 | lead (paused) |
| S8 | reference = dV_frozen2 stage, total, composed with S7; caller adoption waits on S2 | lead (paused) |
| Checkpoint ABI | success-conditioned stage join with the six ordered digest reads proved to dV_frozen2 at the decision position (`CheckpointBytes5Decision.decision_success_join`, 2026-10-22); remaining premises exactly `S2S10CallerBinding` and `S1S7S8StateProvenance` | lead (waits on S2, S1/S7/S8) |
| Parser and multiproof | parser complete against frozen rows; multiproof stage join `both_batches` proved (c), conditional on caller binding and Rust carrier P6 | lead |
| S10 inventory | every declaration assigned; 140 CFG ordering facts kernel-checked; gates exit 2 pending the caller identities | lead (paused) |

## Privacy

**Headline: `privacy_headline_admitted`** (`v8-r0-zk-20261009/lean/R1Z/`, LOG D122).

    ε ≤ 2^-109 + 2^-137 + 2^-454 + 128(M+1)/2^190 < 2^-100,   M ≤ 2^25

Discharged at the protocol instance: causality, the commitment families,
read coverage, history laws, all accounting rows, the wire batch and log
premises, `CallerLaw` (D120), and builder soundness on the admitted input
domain (D122). The simulator cost is relative to the adversary's input:
replay ≤ c·(n+1), cache ≤ C·(n+1)².

**Caveat (D124, 14:30):** at the fixed-observer specialisation the two execution
joins became identities and were deleted, so the headline is a **model-level**
theorem. The deployed claim needs the explicit premise `RustProverRefinement`
below. D111's wire discharge must also be redone over the *ordered* q22 queries,
because the shipped prover batches by order, not by set.

| Remaining premise | Meaning | Owner |
|---|---|---|
| `R_wire_builder_checker_D75_retry` | the shipped prover's whole run (builder, checker, retry) equals the model run outside the named bad event | lead: prover part 15 (observer fixed, QM31 transport, retry history) |
| `G_sim_R_wire` | the source simulator's ideal run equals the model's | lead, after the real-run join |
| `sim_preparation` | concrete preparation cost for simulator efficiency | lead (paused; needs a new env-J range) |
| `RustProverRefinement` (explicit since D125, `PrivacyR1HeadlineDeployed`) | the real shipped prover's whole run (builder, checker, retry, ordered serialisation, observer) equals the constructed source outside the bad event | lead: prover part 16 |
| Ordered-q22 wire encoding | done (D125): ordered 10+12 batches, bound unchanged | — |

**Scope (user, 2026-10-22, LOG D159):** timing and other side channels are inside
the privacy contract. Leakage levels L1 (attempt/retry/error counts), L2
(source-level branch/index/trip-count trace) and L3 (compiled code and
hardware; trust item or measurement only). A side-channel inventory of the
deployed prover is the first step.

## Release gates still to run

1. The cross-cone instance-naming fix (`IMPORT-UNION-20261021.md`), so that
   all cones import together.
2. One canonical frozen-manifest replay, once all cone joins are green
   (AGENTS.md cadence).
3. The `#print axioms` audit on the final headlines.
