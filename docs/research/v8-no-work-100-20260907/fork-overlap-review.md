# Cached fork observations and overlap closure

Research base: `b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`. The new optimized
[`fork_overlap_control.rs`](experiments/fork_overlap_control.rs) is green.
It consumes the eight policies from the frozen
[collector log](experiments/fork-collector-control-v1.log), not a fresh
response/final optimization. Both earlier Rust sources and their evidence
remain unchanged. All execution was local; no NUC, Lean, SBF or production
job ran.

This closes a small **access and evidence-transport** experiment. A shared
oracle cache and four distinct identified folds can certify received slots
without requiring all disclosures to contain a common query support. It does
not solve the far-agreement geometry or establish a witness extractor.

## The necessary distinction: observed versus actual support

For a fixed quotient Q and four or more coefficient-coherent distinct alphas,
the intersection of the **actual full-domain** folded matching sets equals
Q's raw four-slot support. Outside that raw support the discrepancy is a
nonzero cubic in alpha, so it cannot vanish at four distinct values.

Consequently a control with seven coherent finals, fewer than two actual
common fibres, and sound closure recovering two actual matching fibres would
be impossible. The experiment does not manufacture one. It instead uses
**partially observed** matching sets: their intersection can be empty even
when the actual raw support is large. Observed sets are always checked against
the actual received values.

The previously proved [high-region anchor geometry](pre-image-anchor-review.md)
is unchanged. This experiment does not replace its `5*B+cap<T` requirement or
extend its range merely by taking unions of observed supports.

## Implemented data flow

For each fixed prefix the code uses one immutable received-word oracle and
one shared cache. A cache miss reads all four canonical field values of a
fibre; later candidates and records reuse those values. These are explicit
full-oracle model reads, **not authenticated Merkle openings**. The cache is
scoped to one fixed word. Coupling it to commitment binding and a real replay
extractor remains separate.

The diagnostic performs these actual steps:

1. Parse the chosen response, final coefficients, alphas and reported fibre
   masks from the pinned prior log. Reconstruct the same fixed received word
   using the frozen helper model, and verify every reported observation and
   actual carried prior. No optimizer is called.
2. Interpolate candidates from four distinct disclosed finals using a
   rank-four Vandermonde solve. The source checks the determinant and the
   resulting folds. Coefficients use the actual order
   `q[4*lane + alpha_power]`, not evaluation-table entries.
3. Identify **every** other disclosed final whose complete coefficient vector
   equals `Fold_alpha(Q)`. This step depends only on disclosed coefficients,
   not on an assumed anchor or oracle support.
4. Count distinct identified alphas for each observed matching fibre. At
   multiplicity at least four, promote that fibre to a full-slot agreement
   certificate. Check the literal four received slots against Q using the
   shared cache.
5. Reuse each promoted fibre for other finals, even records that did not
   originally observe it. If more than the reduced final-code overlap cap of
   one point agrees, check the implied equality of the two final coefficient
   vectors. Iterate until stable.
6. Only **after closure**, scan Q's full raw support as an independent check.
   That full-support lookup is not used to seed promotion.

The iteration is implemented, but its membership redundancy is important:
when every complete final coefficient vector is already available, step 3
identifies the maximal coefficient-equal cluster for this Q. A sound overlap
check cannot enlarge it. The code asserts and records zero newly identified
finals from overlap. Overlap still verifies the consistency of the slot
certificates, but it is not a new recovery mechanism in this disclosure model.

Four-final interpolation only supplies a candidate. Promotion supplies checked
raw-slot equalities on specified fibres. Neither return value is a valid
payment witness or a universal accepted-execution recovery certificate.

## The eight frozen policies

The input is exactly the eight previously selected policies, not every tied
optimal policy. Their earlier complete tie-aware classification remains in
[fork-collector-review.md](fork-collector-review.md); it was not recomputed.
The new run reconstructs 2,553 distinct candidates from 2,665 four-disclosure
subsets, then executes the new cache and closure logic on each.

| Profile / mode / gamma | Candidates | Largest coefficient cluster | Maximum promoted fibres |
| --- | ---: | ---: | ---: |
| 0 / 0 / 1 | 206 | 5 | 1 |
| 0 / 0 / 2 | 206 | 5 | 1 |
| 0 / 1 / 1 | 310 | 5 | 2 |
| 0 / 1 / 2 | 310 | 5 | 2 |
| 1 / 0 / 1 | 322 | 5 | 2 |
| 1 / 0 / 2 | 322 | 5 | 1 |
| 1 / 1 / 1 | 675 | 5 | 2 |
| 1 / 1 / 2 | 202 | 5 | 2 |

For these frozen policies, the logged observations are all actual matching
fibres of their qualifying finals. Every reconstructed candidate has at least
four coherent observations. Thus the promoted support equals the independently
checked raw support; the code verifies this equality for every candidate.
The image-validity/support histograms match the previous result. In
particular, no image-valid candidate gains two matching fibres, and no
coefficient cluster gains a sixth or seventh member.

The cache uses only **sixteen underlying slot reads per prefix** across all
candidates and all post-closure full-support scans. Its repeated logical fibre
requests are separately recorded; the largest case makes 6,450 requests but
still only sixteen underlying reads. This is cache reuse in an ideal extractor
model, not a CU saving or an authenticated-opening collection theorem.

## New positive control: genuine corruption, partial observations

The producer fixes the image-valid quotient
`[1,2,3,4,5,6,0,0]` and the reduced chord 2x. It encodes this quotient, then
adds **one to all four slots of fibre 3** before any alpha disclosures. The
other three fibres are unchanged. A constant four-slot error folds to one,
so fibre 3 disagrees at every alpha; no favorable cancellation is assumed.

The producer computes the genuine carried compact response for this quotient
and the existing ordinary/image weights. It uses the full compact response
grammar, not the restricted two-free-coefficient adversarial family. The
collector receives only that response, the actual received oracle, and the
seven disclosed finals for alpha 0 through 6. The producer's quotient is
withheld from interpolation and closure, and used only for the final fixture
assertion.

The predeclared observed fibre pairs are

```
01, 12, 02, 01, 12, 02, 01.
```

Every observation is evaluated against the actual corrupted oracle and every
carried prior is checked. Their observed intersection is empty, but the
observation multiplicities are `[5,5,4,0]`. Four disclosures reconstruct Q;
coefficient comparison identifies all seven. The four-observation rule then
promotes fibres 0, 1 and 2, using only **twelve** underlying cached slot reads.
No observation of fibre 3 is needed for those three agreement certificates.

An independent full-support lookup afterwards uses four additional reads and
finds exactly those same three fibres. The actual full matching-set
intersection is therefore `{0,1,2}`, not empty. This is the essential safeguard
that makes the control mathematically consistent.

The seven alphas and observed pairs are predeclared conditional test records.
They are not claimed to have been sampled by a genuine Fiat–Shamir replay or
by independent uniform query draws. The received corruption precedes the
records; no claimed matching fibre is fabricated. This is a legal reduced
oracle/fold/relation control, not a complete component-commitment/OOD/payment
transcript, and no payment semantic or row-extraction theorem is inferred from
it.

There are fourteen successful overlap validations over two closure passes and
zero newly identified coefficient vectors. This is expected: all seven
coefficient-equal vectors were already found directly. The useful new result
is transport of scattered **observed** matches into common full-slot evidence,
not expansion of the actual geometric support.

## Explicit bounds and rejected outcomes

The implementation caps each prefix at nineteen disclosed records, 4,096
distinct candidates and sixteen underlying oracle slot reads. Exceeding any
cap returns an explicit failure rather than a partial success certificate.
The largest actual candidate collection contains 675 coefficient vectors,
whose Rust `usize` payload is 43,200 bytes. That figure excludes BTreeMap and
record overhead; measured peak RSS below includes the process allocation
footprint. The configured coefficient payload ceiling is 262,144 bytes, not
a bound on the whole process.

Seven negative tests check candidate cap, oracle-read cap, record cap,
duplicate alpha, a reported observation on the deliberately corrupted fibre,
a noncanonical final coefficient, and a wrong carried prior. All fail with
their named outcomes. These outcomes are not silently removed from a claimed
extractor probability. Real missing responses, authentication failures and
replay control remain outside this local model.

## Evidence and measurement scope

Reproduction, using a fresh log path:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_fork_overlap_control.sh \
  /absolute/path/to/a-new-overlap-log.log
```

The runner pins the frozen helper source, previous collector source and
previous policy log, then compiles only the new standalone Rust file with
`-O -C overflow-checks=yes`. It uses an independent 1 GiB aggregate RSS guard
and a 90 CPU-second cap. No package or unchanged search is rebuilt or rerun.

| Stage | Exit | Wall time | Peak RSS (bytes) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Optimized standalone compile | 0 | 1.27 s | 175,276,032 | 0 |
| Cache/closure diagnostic | 0 | 0.41 s | 1,982,464 | 0 |

Internal arithmetic time was 0.00507 s. Rust was
`1.93.0 (254b59607 2026-01-19)`. The retained compile log includes one benign
warning about an overwritten initial counter assignment; no proof or runtime
check failed and no unchanged rerun was launched to remove the warning.

SHA256 pins:

- New source: `9a914ca5342d14cc891c29d6d3c91b03a8d75155fb8211ca8406c60aa335783e`.
- Runner: `ecead07c017c5e479b11a399b70c480d1bab97855c364bbf678951c1bd0b887a`.
- [Green log](experiments/fork-overlap-control-v1.log):
  `3c815ce489e8eb978f17c16e464afa2c78d52f84a326f2e968f3e7ed39bfbbb3`.
- Consumed frozen policy log:
  `c27b8b773976576c1b054accb437758152f2fde83d357f68e0b888004526d167`.

This is exact executed Rust evidence, not a new Lean theorem. It changes no
field, query schedule, proof messages, masks, verifier acceptance or
production defaults. The 40,282-byte maximum body is unchanged. Oracle cache
reads are not proof bytes or verifier CU; no new proving or complete-transaction
measurement is reported.

## Decision

Shared observations can recover usable slot evidence even when their observed
intersection is empty. Keep this data-access mechanism. It does not repair the
eight rotating-support policies or supply a numerical bound on their accepted
unrecovered mass.

With fully disclosed final coefficients, further overlap iteration alone
cannot expand a quotient's coefficient cluster. The next substantive step
must either combine information across genuinely different causal prefixes
with proved bindings, supply a different recovery procedure, or bound the
remaining accepted failures. It must not rebrand observation-cache growth as
new full-domain agreement or charge the entire far class as knowledge failure.
