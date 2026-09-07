# Review of the fixed-target Lean milestone

This pack reviews Aspis commit `1803896acf5d8c4ebe769b3927010031faf40e0e`.
It does not modify a repository, contain a completed adaptive security proof,
or claim V8 CU parity or zero knowledge.

## Inspected evidence

At that revision:

- `docs/research/v8-no-work-100-20260907/lean-repair-review.md`;
- `experiments/FixedTargetQuerySupport.lean` in that research directory;
- `lean-repair-evidence.json`;
- `crates/aspis-core/src/v6_query_batch.rs`.

The Lean leaf's fixed-target experiment is explicit and its bad-fibre witness
is constructed, not imported from a successful provider. Its recorded replay
audits 17 declarations with `propext`, `Classical.choice`, `Quot.sound`, no
new axioms and no sorry. This pack inspected that record but did not run Lean.

The source's shifted batch includes the prior discrepancy as a constant.
General q22 cancellation is therefore 22/(k-1), not automatically 21/(k-1).
The script contains an exact 22-root algebraic sharpness example.

## Independently recomputed arithmetic

For k=(2^31-1)^4, T=262144, J=9557, q22:

| Fixed-target quantity | Display bits |
|---|---:|
| All queries common | 105.1420996194 |
| Pointwise pass with wrong queried support | 119.0458036869 |
| Total pointwise pass | 105.1420054893 |
| Pointwise plus general shifted-rho cancellation | 105.1419386911 |
| Plus recorded 396430/(k-1) inventory, conditionally | 104.2667058229 |

Changing rho's numerator from 21 to 22 adds exactly 1/(k-1) to this screen,
reducing its displayed security by approximately 0.00000165524 bits. The
logical correction is important; its numerical cost is not the bottleneck.
The 396430 inventory and all other terms must be re-established for any new
adaptive partition. It is not labelled purely semantic here.

## Next formulation

`NEXT_ADAPTIVE_GATE.md` proposes conditioning at the genuine fresh-query
boundary. The actual final candidate may depend on earlier gamma/alpha. For
its matching-fibre count M and a valid pre-query outside event O, the exact
pointwise accepted-outside probability is

    E[1_O * choose(M,q)/choose(T,q)].

The tail version is a finite hockey-stick identity. It is a way to organise a
needed adaptive proof, not the missing proof: quantitative bounds on the
outside-candidate agreement tails, actual event/source correspondence, privacy,
and random-oracle resource lifting remain unresolved.

## Executed in this environment

Run:

    python3 check_adaptive_queries.py > results.json

Standard-library Python only, exact integers and rational comparisons.
Floating logarithms are display fields.

The run passed 3,586 exhaustive match-set/subset and binomial-tail cases,
4,096 weighted two-prefix/outside-event cases, the distinct 22-root shifted
batch instance, and a countermodel to conditioning on a target chosen AFTER
the query schedule. Both historical all-zero-fibre subevents are recorded
only as subevents, not as full acceptance or complete folded supports.

There is no Lean/lake or Rust toolchain in this environment. No Lean source is
presented as compiled; no Rust/SBF, full prover, rank elimination, source write,
remote job or deployment was performed.
