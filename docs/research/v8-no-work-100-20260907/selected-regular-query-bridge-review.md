# Regular higher-Y prefix to the actual alpha/query event

Status: kernel checked on the NUC, v7, exit 0. The leaf is
`experiments/SelectedRegularQueryBridge.lean`; all seven printed theorem
audits use only `propext`, `Classical.choice`, and `Quot.sound`. The final
log has no errors, warnings, or `sorryAx`. It records 4.86 s wall time,
6,840,004 KiB peak RSS, and zero swaps. This is a scoped query-event bridge,
not complete higher-Y soundness or source/Fiat--Shamir coupling.

The original source-review comment inside the frozen Lean source is retained
unchanged; this report records the subsequent successful check. Source-work
parent:
`96046bac27e443a67cd4a3820d1c0801f94816fa`.

Final source and v7 immutable source-snapshot SHA256:
`a989bb3fcc17667e08a730cba002c499d2b71f8c06751ef92a79247004e68b02`.

Final olean SHA256:
`f864c92123f037338347ead9e6c9fe01d811e1ad90a1231692d573722750b6f8`.

V7 log SHA256:
`2200af1c487cbaefe23d885ce08ff60dcfd33749f34dd81fa87ff99d4e02c169`.

V7 manifest SHA256:
`e5ac559ea9ba1feefc6f3157eefa8fdcbcfbcf22611882d62d0bf03772c2d87f`.

Dependency provenance caveat: the v7 manifest omits the restored direct
import `FoldSupportClosure`. Its exact pair and old checked dependency
boundary were verified read-only after this run, as documented below. The
recorded `OVERLAY_PROVENANCE_PASS=923` does not cover that omitted pair.

## Focused checks and retained failures

All seven attempts' exact `.log`, `-manifest.json`, and `-source.txt`
artifacts are retained locally under
`experiments/selected-regular-query-bridge-nuc-v1` through `-v7`.
The green `SelectedRegularQueryBridge.olean` is also local. Retrieval used
Tailscale SSH/SCP to `dombarker@100.108.41.90`, with `BatchMode=yes`,
`ConnectTimeout=10`, `StrictHostKeyChecking=yes`, and
`HostKeyAlias=nuc.local` for the existing host key only. All 23 remote/local
SHA256 comparisons passed: 21 attempt artifacts, the green olean, and the
already-present final source. Every source/manifest digest also matches its
own attempt log; the final source equals the immutable v7 snapshot.

| Attempt | Exit | Wall seconds | Peak RSS, KiB | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 0.93 | 2,133,692 | 0 | Missing `FoldSupportClosure` import; no declaration check. |
| v2 | 1 | 23.11 | 6,845,320 | 0 | Restored import; missing `storedPoint` name, local conversion heartbeat failure, positivity recursion and final addition-order mismatch. |
| v3 | 1 | 15.99 | 6,845,252 | 0 | Local query conversion heartbeat failure and final addition-order mismatch. |
| v4 | 1 | 16.95 | 6,812,904 | 0 | Local query conversion still exhausted 250000 heartbeats. |
| v5 | 1 | 4.65 | 6,806,828 | 0 | Residual/`Matches` conversion reached recursion depth 200. |
| v6 | 1 | 4.53 | 6,834,288 | 0 | Explicit conversion exposed only missing `exactFinalLinear` namespace. |
| v7 | 0 | 4.86 | 6,840,004 | 0 | Seven standard-only audits; both recorded 923-entry provenance checks passed. |

The replacement proof uses the actual schedule coordinate equality followed
by named final-evaluation/oracle-fold rewrites and explicit residual target
types. Nonnegativity and the final sum comparison use direct named lemmas.
No theorem statement was weakened and no source recursion/heartbeat or
resource cap was raised: all seven snapshots retain `maxRecDepth 200` and
`maxHeartbeats 250000`. V1 and v2 intentionally have identical source and
manifest digests; the missing-import environment was restored between them.
Failed attempts, including their placeholder `sorryAx` diagnostics, are not
credited as checked exports.

The inherited task is
`/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`; its runner creation
pin remains `289d7356c78a4cd493fe61a54f9548f2a0c11298`, distinct from the
source-work parent above. Borrowed V7 source pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, Lean 4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and native Mathlib cache pin
`81a5d257c8e410db227a6665ed08f64fea08e997`. Runner SHA256 is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The recorded compiler command is:

```text
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean -j1 -M9500 -R /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/overlay -o /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/overlay/SelectedRegularQueryBridge.olean /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/overlay/SelectedRegularQueryBridge.lean
```

Its actual v7 cgroup values are `memory.high=8589934592`,
`memory.max=10737418240`, `memory.swap.max=0`, and
`cpu.max=200000 100000`. `PROVENANCE_UNCHANGED=true` closes the successful
log, subject to the omitted-import boundary below. Native package artifacts
were reused, not rebuilt. This evidence-retention update ran no compiler,
did not modify theorem source or old manifests, and did not touch unrelated
remote jobs.

## Exact next bridge

Fix the actual execution's C1, C2, completed OOD data, a factor F, one OOD
row r and gamma. The existing regular-branch uniqueness theorem identifies
every `Qualified` quotient on this branch. Consequently, if any later
kappa/tau/alpha history has `fixedRegularPrefix`, there is one Q such that
every such history's actual final equals `coefficientFoldLayer 256 alpha Q`.
The existential Q precedes the universal quantifier over these histories.
This is an analysis consequence of regularity, not a change to prover timing.
In particular, it supplies no polynomial-in-gamma candidate or pre-gamma
component tuple.

The new interfaces are:

| Declaration | Exact scope |
| --- | --- |
| `fixed_regular_final` | Identify an actual qualifying final using any fixed qualified Q at this gamma. |
| `exists_fixed_regular_final` | Construct that fixed Q from existence of an actual regular prefix, before all later histories. |
| `actual_query_matches_iff` | Transport the same ordered field-domain schedule to its literal indexed fold residuals. |
| `nonfull_schedule_alphas_le_three` | A schedule containing one non-full Q fibre has at most three all-matching alphas. |
| `regular_nonfull_schedule_alphas_le_three` | Retain the actual adaptive final and regular-prefix indicator in that count. |
| `regular_matching_moment_bound` | Export the matching-only comparison, for use after one global acceptance reduction. |
| `fixed_regular_suffix_bound` | Bound actual restricted compact-suffix acceptance by the fixed-Q joint alpha/query moment plus q/|G| + 18/|A|. |

The prefix contains the actual literal-family quotient, image equations,
same-factor root, correct anchor rows, and actual folded-final equality.
Regularity is evaluated at this gamma on the actual OOD row. The uniqueness
proof additionally uses checked OOD reconstruction, the two circle
equations and exclusion of the west pole. It does not require a new factor
certificate, candidate curve, source correspondence, or gamma support
threshold. The existing `regular_prefix_support` separately derives 38230
original matching symbols from this same prefix.

## Why both collision mechanisms must remain

Full raw-fibre agreement implies folded agreement at every alpha. The
converse is false. At any actual nonzero circle coordinates x,y, raw-slot
discrepancy `(1,-1,0,0)` has fold

`alpha/(2*y) + alpha^3/(2*x*y)`.

It vanishes at alpha=0 while the raw slots are not equal. This is a direct
algebraic obstruction to deleting all non-full schedules. It is not claimed
as a full regular-prefix or accepted-source forgery. The checked leaf uses the
already checked `four_identified_matches` theorem to retain the correct
at-most-three alpha roots for each such schedule, with no union over its
query positions.

Terminal acceptance also does not imply pointwise query residual zero. For
example, a nonzero residual polynomial `1-X/rho0`, with nonzero rho0 and
zero prior, vanishes in the shifted batch at rho=rho0. Subsequent honest
relations can then accept. The existing `RelationCompatibleMoment` theorem
is exactly the appropriate reduction: retain prior-zero and all-query-match
mass, then charge the actual shifted batch and three later degree-six
repairs. This explains the q/|G| + 18/|A| term; no first-stage 6/|A| charge
is introduced here.

## Exact composition, not a product of marginals

Let s be this Q's number of full raw fibres, T=262144, and
`b = choose(s,q)/choose(T,q)`. The actual ordered distinct schedules have
this same all-full ratio: q! cancels by `ordered_matching_ratio`. Exchanging
the two finite sums, then applying the per-schedule cubic bound, gives the
next purely finite-count consumer

`E_alpha[matchingRatio(Fold_alpha(Q), Fold_alpha(received))]`
`<= b + (1-b) * min(1, 3/|A|)`.

That displayed normalized count is a mathematical consequence of the
exported schedule bound and existing schedule counting; it is not yet an
exported theorem of this leaf. In particular, the present checked claim is
not advanced to a new numerical soundness bound.

For a factor union, first apply the existing supported suffix reduction
ONCE to the union event. Then partition/count its matching moment using
`regular_matching_moment_bound`. Do not sum the per-factor suffix corollary
and thereby repeat q/|G| + 18/|A|. Cubic alpha collisions belong to the
factor/query counting itself and are not silently absorbed into an already
charged unrelated collision term.

Likewise, summing over gamma must retain the actual support s(gamma).
The existing incidence tail and the binomial query function can be composed
by exact finite layer counting; their marginal probabilities must not be
multiplied. Complete-fibre to original-symbol transport supplies at least
4*s-2 original symbols (two SYMBOL poles, not two fibres). Thus a full-fibre
tail at t can consume the existing regular incidence denominator
`(4*t-2)-1024 = 4*t-1026`. No degree-two bound is substituted for the
degree-28 ordinary/OOD claim error. C1 remains fixed early, while the actual
three-helper curve is still degree two.

## Reused boundaries and remaining obligations

Direct imported source pins:

- `CausalHigherYClassification.lean`:
  `b8ab80aa4036cfb0cca428d68676c1bf3c9072f5671cc39f9fe10923d0b7c1fa`.
- `SelectedOriginalInjectivity.lean`:
  `f4bf9122dc43eba2266f8fe626b17f66d9849d67689ed7210f3d178217ecdbf8`.
- `FoldSupportClosure.lean`:
  `6533b4b6ad8c232c4a8bd87e13f2de7837dd125b316a257d2b7dea4bb968963d`.

The inherited suffix source is `RelationCompatibleMoment.lean`, SHA256
`46bcc1742e832f54dd075da6b13a69c859d46daf3951ab6928f8b4dc6b52c726`.
The v7 manifest pins `CausalHigherYClassification.olean` as
`9d72fdd0dc855c511abeb26cd9cc7f193275988de70dd5aa249c4f29fd28e545`
and `SelectedOriginalInjectivity.olean` as
`102b5e58658ddcaf2436c23fd9986d25a315f9ec518249b132c374c7611e5d06`.
Their source/output pairs and `RelationCompatibleMoment`'s pair were also
verified against the current remote overlay during read-only retention.

### Restored import omitted from the run manifest

Neither the v1 nor v7 immutable manifest contains `FoldSupportClosure`.
The restored current NUC source/output pair was independently hashed and
matches the exact local artifacts and old successful
`experiments/fold-support-closure-v2.log`:

- Source: `6533b4b6ad8c232c4a8bd87e13f2de7837dd125b316a257d2b7dea4bb968963d`.
- Olean: `a2fddf05f2887f0468b4b4b6e017612dbfed10e4a01839735103336987544926`.
- Old checked log: `7f242d92e4b6c73ae37245c16295cdaac5f3a527e74d1856d7250d1f0b08291d`.

The source also matches its committed blob at `96046bac`. The old proof and
seven standard-only audits are documented in
[fold-support-closure-review.md](fold-support-closure-review.md) and the
existing `off-family-tail-evidence.json`; neither was modified or replayed.

Its only direct import, `SevenAlphaRecovery`, has source SHA256
`c36bd88630d0529bfd330b5341b6763c5db8859cc7e7b91538bbd04717f3ad21`
and olean SHA256
`cbf44c42d7d85eba1bb3e60142a194368f7d919e8512e6a4f3afbff351390b1c`.
Both exact hashes occur in the old FoldSupportClosure build log and the v7
manifest, and match the current remote bytes. Thus the present restored
pair and its direct checked boundary are identified without rebuilding.
These are POST-RUN byte/provenance checks, not a retroactive claim that v7
preflight hashed the missing pair. No execution-time copy receipt was
available, so that historical manifest gap remains explicit.

Remaining beyond this leaf: the normalized ordered-count consumer; the
one-time union/tail aggregation; integration of singular higher-Y events;
the retained original-tuple/payment-extraction alternatives; and literal
commitment/source/random-oracle coupling. The finite ideal challenge/query
law used by the existing game is not obtained from freshness by naming this
a causal prefix. Prior frozen proofs and their evidence were not modified.
