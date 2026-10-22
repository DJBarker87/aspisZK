# Security contract (binding), 2026-10-21

This note reconciles the completion criterion used by every session. It
supersedes any shorter wording in other notes, including the lead's port
adoption addendum in `C3-BIN-20261021.md` (see the correction below).

## The user's target (recorded 15 October; reaffirmed 21 October)

From `TARGET-CLARIFICATION-20261015.md`: **"100-bit per-attempt soundness,
without grinding credit."** On 21 October the user added that the goal is
**classical security in the same units as Zcash's quoted 126 bits**, with
repeated attempts properly accounted for and no grinding credit or
work-normalisation tricks.

Operationally, completion means both of the following, proved for the
deployed verifier:

**(A) Per-attempt error.** One transcript attempt under the protocol's
challenge experiment fails, meaning a false statement is accepted, with
probability ≤ 2^-100. No proof-of-work bits count toward this, and no
probability is divided by adversarial work.

**(B) Repeated and adaptive attempts, stated plainly.** For an adversary
issuing at most Q oracle queries, counting repeats, the total failure
probability is bounded by an explicit expression that keeps its Q-dependence,
of the form (attempt starts) × B + collision mass. In particular, for an
adversary that makes no queries of its own and submits a single proof, the
bound must itself be ≤ 2^-100, which is (A) at the level of the whole
experiment. The bound must not be restated as a per-query rate in place of (B).

The Zcash comparison follows from (A) and (B) together. An attack doing W
hash evaluations succeeds with probability at most about W·B, so the attack
work needed for success probability near 1 is about 1/B ≈ 2^105. That is a
consequence used for communication, not the completion criterion.

## Where each endpoint stands against the contract

| Endpoint | Per-attempt mass B | Bound with no adversary queries | (A) | (B) |
|---|---|---|---|---|
| `R1FinalSoundnessHeadlineV3` (pure decision) | 15/2^109 ≈ 2^-105.09 | (0+34)·B + κ ≈ 0.996·2^-100 | met | stated |
| `OraclePortHeadlineFrozen` (adopted port) | 15/2^109 ≈ 2^-105.09 | (0+1080)·B ≈ 2^-95.0 | **not met** at the whole-experiment level | stated, with Q+1080 |
| `OraclePortHeadlineFrozenPerAttempt` (probability-level repair) | 15/2^109 ≈ 2^-105.09 | 34·B + κ(1161) + 2^-126 + 2^-454 ≤ 2^-100 | **met, conditional** | stated, with Q+34 for every Q |
| `OraclePortHeadlineFrozen2PerAttempt` (two-transaction checkpoint model) | 15/2^109 ≈ 2^-105.09 | 34·B + κ(1161) + 2^-126 + 2^-454 ≤ 2^-100 | **met, conditional** | stated, with Q+34 for every Q |

All four are conditional on their source premises. None is release-complete
for the deployed verifier until those are discharged. In particular, the single-pass `OraclePortHeadlineFrozenPerAttempt`
endpoint retains exactly `hqueries`, `AcceptedRunJoin D rust` and
`StoredCarrierBinding D rust P runtime`; its premise signature diff is empty.

The port's 1080 counts verifier-issued terminal Merkle reads as potential
attempt starts. This is a counting artefact of the union bound, not an attack.
A compiled counterexample (`ROWAWARE-DRAFT-20261021.md`) shows that such a
read can be recognised as a fresh start by the decoder, so the decoder-level
fix failed. The probability-level repair is proved in
[`START-CHARGE-20261021.md`](START-CHARGE-20261021.md): the submitted
transcript's starts are already read in the prover/sampler prefix, before
terminal authentication. The restricted hit event has mass at most
(Q+34)·B under the unchanged full adaptive experiment. The collision mass
κ(Q+1161), extractor abort 2^-126, and query-scan exhaustion 2^-454 remain
unchanged. `OraclePortHeadlineFrozenPerAttempt.failure_bound` states their
full sum for every Q; `zero_queries` proves (A) at the whole-experiment
level. `per_query` retains the old Qmax with no positive lower bound on Q.
No decoder, shipped implementation, security metric or adversary restriction
changes. The old adopted endpoint itself remains unchanged.

## Correction to the lead's adoption addendum

The C3-BIN addendum "oracle-decision port ADOPTED" (2026-10-21 09:40) gave the
target as "(Q+1)/2^100". That is a corollary, not the contract, and under the
port it holds only for 32 ≤ Q ≤ Qmax. The binding criterion is (A) and (B)
above. The unchanged `OraclePortHeadlineFrozen` endpoint must not be described as
meeting 100-bit per-attempt soundness. `OraclePortHeadlineFrozenPerAttempt` provides
the conditional single-pass probability repair; correspondence to the deployed verifier
and the runtime carrier binding remain outstanding.


## Two-transaction model target

The additive `OraclePortHeadlineFrozen2PerAttempt.final_soundness` targets
`OraclePortFrozen2.dV_frozen2`, including checkpoint save and authenticated
resume between batch 0 and batch 1. Its source premise is the newly targeted
`OraclePortFrozen2Join.AcceptedRunJoin D rust`; it retains the original
`StoredCarrierBinding D rust P runtime` and adversary query-count hypothesis.
Boolean acceptance equivalence does not convert the old single-pass source
join into this new ordered-log join. The old endpoints remain separately
named historical model theorems.

The verifier envelope remains 1161: a symbolic one-resource-per-slot
improvement pays for the six extra checkpoint digest reads. First reads
remain at most Q+1161, and the recorded log is at most Q+2322. Submitted
transcript starts are already followed in the prover/sampler prefix, before
all checkpoint digests, so the start charge remains Q+34. Digest inputs need
not be syntactically disjoint from the decoder language.

`failure_bound` states the full repeated/adaptive-attempt expression, and
`zero_queries` proves the whole-experiment ≤2^-100 inequality. The extractor,
B, collision function, abort allowances, query range, adversary and security
metric are unchanged. See [DV-TWOTX-20261021.md](DV-TWOTX-20261021.md) and
the receipts under `evidence/dv-twotx-20261021/`. This is a conditional model
endpoint. The deployed security target is **not yet established**: the new
frozen-source accepted-run join and runtime/carrier binding remain open.
