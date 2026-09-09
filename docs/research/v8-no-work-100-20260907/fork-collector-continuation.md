# Fork recovery: row separation and evidence collection

Research parent: `532ade2064e533602902fc9ae5b4dd90f9207131`.
Branch: `research/v8-no-work-100-20260907`. Laptop-only continuation;
the NUC thermal pause was respected. Host: Apple M3, 24 GiB RAM,
macOS 26.5 (25F71), arm64. No verifier or production code changed.

## What changed

`FourKappaRecovery` completes deterministic separation of the repaired four
ordinary rows on the **same constructed quotient**. Given a qualifying
common-support fork grid, it derives the inactive claim and all three point
claims, as well as both image constraints. It does not assume inactive
exactness, supply a quotient, or freeze adaptive finals before alpha.
See the [theorem and replay scope](four-kappa-recovery-review.md).

The bounded collector experiment makes the remaining access problem concrete.
In all eight predeclared reduced-game prefixes, a maximizing causal response
has 10–13 useful alpha continuations, but no common two-fibre group across seven
alphas. Even accounting for every tied maximizing response and every compatible
final choice, the largest such group has only four or five alphas. Counting
useful continuations is therefore not a substitute for collecting coherent
ones. These are exact restricted F19 controls, not a QM31 attack or a claim
that extraction is impossible.

Conversely, the positive controls recover an image-valid quotient from four
disclosed finals without being given its coefficients. All 19 final branches,
received slots, carried priors and image/ordinary equations are then checked.
This is an explicit full-oracle model, not Merkle authentication or a real
Fiat–Shamir replay extractor. The [collector report](fork-collector-review.md)
records the exact interface, ties and failure outcomes.

## New collection information, with the right event

Fix one actual final/query prefix and let U be the union of retained,
root-bound, pointwise-checked query indices. Each fresh q22 schedule is uniform
conditional on the entire history in the stated ideal experiment. The choice
to retain it may depend on that schedule and later responses.

If the final union has at most 255 indices after at least **235** retained
continuations, some retained schedule added no new index. The first schedule
adds 22; 234 strictly growing successes can fit exactly 255 indices, but 235
cannot. At any history whose union is at most 255, the probability of such
a non-growing fresh schedule is at most

```
b255 = choose(255,22) / choose(262144,22).
```

Thus over at most N actual fresh draws, the joint event above has probability
at most `min(1, N*b255)`. The displayed one-draw value is about `2^-221.4682`.
This is a union over the collector's draws, not a query-location loss or
grinding credit. It includes rejected/aborted draws in N and does not condition
on obtaining 235 successes. Accepted-only queries need not be uniform.

The small exact backward-induction program allows every causal retain/discard
strategy after each fresh query. It verifies this bound in 108 games with
domains of at most eight points and tests the sharp growth threshold and
censoring counterexample. This finite test is not the universal probability
proof. The symbolic derivation and prerequisites are in the
[collector support analysis](collector-support-review.md); the deterministic
set-growth part is [kernel checked](censored-collector-growth-review.md).

The result removes one avoidable access obstacle: after sufficiently many
qualifying successes, tiny support caused solely by repeated/censored queries
has a bounded probability. It does **not** ensure enough successes, or common
support across different alpha/tau/kappa finals. The latter is exactly what
the reduced-game experiment distinguishes.

## Existing geometry reused, not reproved

`PreImageAnchor`, `PreImageAnchorSelected` and `PreAnchorJoint` already give
the sparse-alpha/pre-tau-anchor dichotomy when `5*B+255 < 262144`. The generic
statement includes B up to 52,377; this is arithmetic about an existing
theorem, not a new high-region security claim. It already identifies every
sufficiently close final and charges bad image/row anchors jointly.

Its good-row anchors still need component/payment recovery; farther finals
retain their mass. It does not justify assuming that a fixed family covers
every adaptive candidate. The present collector work targets that remaining
coherence/access issue, instead of repeating the high-agreement argument.

## Updated extraction obligations

The target remains `Pr[A AND NOT X]`, where X is a bounded extractor returning
a witness checked against authoritative payment/context/settlement inputs.
The following is an implementation/proof obligation map, not a completed
partition of actual verifier executions.

| Stage / event | New result | Still required |
| --- | --- | --- |
| Fixed committed word, replay and canonical disclosures | Tiny oracle collector rejects identity, duplicate, cap and canonical errors | Actual V8 root-bound access, fixed prefix restoration, source coupling and all failure probabilities |
| Many accepted but very small one-final support | Sharp growth implication and censorship-safe bounded-draw argument | Genuine conditional fresh sampling and enough qualifying successes within declared caps |
| Useful alpha continuations | Exact control shows 10–13 need not supply seven coherent ones | A quantitative coherent-family/overlap collection theorem, not a success-count assumption |
| Qualifying 4-kappa × 3-tau × 7-alpha grid | One recovered Q, both image constraints and all four ordinary claims | Probability/resources of producing the grid or a weaker sufficient recovery certificate |
| Gamma/component recovery | Prior fixed-C1 degree-two helper and degree-28 claim reductions retained | Accepted far-family coverage, component causality and earlier lambda/chi binding |
| Payment witness | Existing coefficient/layout/payment prerequisites retained | Actual accepted constraints imply checked witness recovery for the specified extractor |

Scalar acceptance with nonzero prior or nonzero pointwise residual remains
visible. The shifted degree-q rho term and three later relation repairs in
`RelationCompatibleMoment` are still counted once. They are not inferred away
by the collector's filter. Its new stagnation event is an extractor-resource
event, not an additional independent protocol soundness component.

The seven/three/four root arguments are deterministic after observing a fork
grid. They do not provide fresh 6/k, 2/k or 3/k estimates against a quotient
chosen from those same forks. No complete numerical bound for remaining
accepted extraction failure is available; the machine-readable ledger leaves
it null rather than filling it with an arbitrary small term.

## Cost, privacy and decision

The body is unchanged:

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

No new public messages, verifier operations, SBF measurements or full-transaction
CU results are introduced. Disclosures and oracle reads belong to the private
extractor model, not hidden proof-body additions. New tests use only synthetic
small-field data. Full-view ZK and the resource-bounded FS lift remain separate,
including nonce selection, prequeries, retries, forks, restorations and fuel.

QM31 q22 remains worth pursuing: the corrected relation's deterministic
recovery endpoint is stronger, and no verifier/profile change was needed.
The stopping condition for this *particular common-support strategy* is now
explicit: a lower bound only on useful continuation counts is insufficient.

The single next experiment should test a **coherent-family or overlap-closure
collector**, not demand the same support from every useful final. It should
retain all adaptively chosen finals and their actual relation priors, recover
Q from four disclosures, then identify further finals only through checked
overlaps greater than 255 (or a proved alternative). Its failed branches and
finite replay cost must stay in the accepted-extraction ledger. A bound on
that collector's failure, rather than another isolated root count, is the
decisive remaining mathematical step for this route.

Commands, hashes, axiom audits and measurement scope are recorded in the
focused reports and `fork-collector-evidence.json`. No unchanged large replay
was run; source caches were checked against the immutable borrowed V7 pin.

| Focused job | Exit | Wall | Peak RSS | Swaps |
| --- | ---: | ---: | ---: | ---: |
| FourKappaRecovery v1 | 0 | 50.22 s | 5,314,445,312 B | 0 |
| CensoredCollectorGrowth v2 | 0 | 0.92 s | 1,309,573,120 B | 0 |
| Optimized collector control (excluding compile) | 0 | 0.51 s | 2,277,376 B | 0 |
| Tiny exact censoring-policy control | 0 | 0.22 s | 20,430,848 B | 0 |

The growth leaf's first attempt had one local `subst`/equality-projection
error; its failed log is preserved. The corrected v2 uses the same memory
cap. All eight retained declaration audits across the two new leaves contain
only standard Lean axioms. Imported source/olean hashes for FourKappa were
also compared with the earlier green ThreeTau closure, not merely today's
source files. The collector compile took 1.38 s and 168,886,272 B peak RSS.

Read-only evidence audit (no proof or Rust rerun):

```sh
python3 -B docs/research/v8-no-work-100-20260907/experiments/audit_fork_collector.py --check-recorded
```

The optional tiny-policy reproducibility check is:

```sh
python3 -B docs/research/v8-no-work-100-20260907/experiments/censored_collector.py --check-recorded docs/research/v8-no-work-100-20260907/censored-collector.json
```

The individual focused runners refuse to overwrite existing logs. A future
justified replay must use a new path. These host measurements are formal
checking and diagnostic execution, not proving or actual extraction latency.

Both read-only evidence checks and all three `bash -n` runner checks passed.
The unrestricted staged whitespace check flags only the already executed
FourKappa runner's trailing blank lines. Those bytes are retained to preserve
its recorded hash; the scoped check passes with `blank-at-eof` disabled.
