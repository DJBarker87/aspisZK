# Actual low-branch finite probability composition

Checked source:
[SelectedRegularLowProbability.lean](experiments/SelectedRegularLowProbability.lean).
Focused NUC v3 is GREEN: exit 0, 3.44 seconds, peak RSS 6,894,792 KiB,
zero swaps and five standard-only axiom audits. Its only direct import is
the frozen green `SelectedRegularLayerCakeInstance`; the required older
averaging and source-game interfaces are already in that import closure.
No predecessor source or report was changed for this composition. The green
source and copied evidence are frozen.

## Exact event and conclusion

`lowProbability e A G Gamma` is literally

    avg_{gamma in Gamma} avg_{kappa in G} avg_{tau in G} avg_{alpha in A}
      (if LowPrefix e gamma kappa tau alpha
       then suffix e gamma kappa tau alpha A G else 0).

It retains the actual source final `(e.strategy gamma kappa).final tau alpha`
and the complete compact suffix. It is not a scalar equality probability,
a replaced strategy, or a query-only event.

`low_probability_bound` concludes

    lowProbability <= 117049/|Gamma| + integratedBudget(q,Gamma,A)
                        + q/|G| + 18/|A|.

The inherited integrated budget includes the single conservative 3/|A|
alpha term and the exact multiplicity-preserving layer cake on fibre
support [9558,200807]. No factor-count multiplier is introduced here.

The caller supplies only the existing checked OOD data/circle/non-west
conditions, nonempty A,G,Gamma, q>0, q<=262144, and the explicit
`6752623450 <= Gamma.card` comparison. It also retains the outside branch
of the full pre-OOD singular-product pair-root event:

    NOT (for both actual rows r,
      SelectedSingularOODFamily.obstruction(c1,c2)(point(data,r)) = 0).

This is not an assumption that either independent OOD label is fresh.
The opposite pair-root branch is not bounded by this leaf.

## Root-first source integration

1. `exists_common_row_bound` constructs one row r and nonzero Z with at
   most 117049 roots in the ORIGINAL finite Gamma. Its actual low-event
   inclusion and matching bound hold uniformly for all later kappa/tau.
2. `low_slice_unit` uses `CausalOrderedRelation.after_unit` under the
   three literal later means to show actual low-event suffix mass <=1
   on every gamma, including a root of Z. No scalar acceptance proxy
   replaces the suffix on these histories.
3. On a nonroot gamma, `nonroot_slice_bound` proves LowPrefix is exactly
   the existing regular-low union: the forward implication is the derived
   common-row inclusion; a regular-low witness contains LowPrefix by
   definition. It applies `SelectedRegularLowSupport.shared_suffix` ONCE
   to that union and rewrites its matching moment to the gated unionScore.
4. Root gammas are bounded by one plus the nonnegative gated moment and
   repair. Averaging this pointwise inequality produces the actual root
   indicator divided by the unchanged Gamma.card. The root-set cardinal
   bound gives the displayed 117049/|Gamma| term.
5. `moment_average_bound` uses the already checked
   `RegularQueryMoment.Generic.avg_commute` twice to reorder the original
   finite gamma/kappa/tau/alpha means into kappa/tau/gamma/alpha. The
   uniform selected gamma/alpha bound is then averaged over kappa and tau.
   The repair is a constant under all these means, so it is charged once.

These are rearrangements of a defined finite product experiment. They do
not infer independence or a probability product from marginal estimates.
No gamma domain is filtered and renormalized; both exceptional and regular
histories keep the same denominator.

## Boundaries

The fixed early C1, actual quadratic helper curve and full degree-28 claim
timing are inherited unchanged from Execution. No successful early decoder
is required for this low branch, and none is inferred. The earlier
representative construction remains analysis-only: it never freezes the
adversary's final before alpha.

This is a low higher-Y branch result, not a bound for all covered or all
accepted executions. The separate high-support branch and pre-OOD pair-root
alternative remain outside it, as do actual sampler/ROM/Fiat--Shamir
coupling, authentication, payment validation and extraction. A later global
partition must avoid charging the same shared suffix term once per separate
covered class; this theorem's repair is once for its whole LOW union only.

No new finite-field computation, enumeration, compiler-limit increase or
package replay was performed. Verification targeted this single new leaf
under the existing capped NUC runner.

## Verification and preserved attempts

| Attempt | Exit | Wall time | Peak RSS (KiB) | Swap | Outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.28 s | 6,859,204 | 0 | Two local transport failures |
| v2 | 1 | 3.22 s | 6,859,948 | 0 | One named-expression rewrite failure |
| v3 | 0 | 3.44 s | 6,894,792 | 0 | Five standard-only audits |

V1's simplification did not equate the ungated matching function with
`unionScore`, and its generic cast tactic exposed two equivalent concrete
field-instance paths. V2 replaced these with a pointwise equality proved by
regular/nonregular cases and the explicit natural-to-rational inequality
`Nat.cast_le.mpr roots`. Its only remaining failure was rewriting that
equality where the source theorem contained the expanded `compatibleMoment`
but the equality contained the abbreviation `prefixMoment`.

V3 adds exactly one line: `dsimp only [prefixMoment] at momentSame` before
the rewrite. This expands only that named expression, retaining the
pointwise proof. It changes no hypothesis, theorem conclusion, event,
arithmetic budget or resource limit. Failed-run `sorryAx` entries are
diagnostics, not theorem credit.

All five v3 declarations—`low_slice_unit`, `moment_slice_nonneg`,
`nonroot_slice_bound`, `moment_average_bound`, `low_probability_bound`—use
only `propext`, `Classical.choice`, and `Quot.sound`. The run uses Lean
4.32.0, `-j1 -M9500`, depth 200 and 250000 heartbeats, cgroup
MemoryHigh=8589934592, MemoryMax=10737418240, MemorySwapMax=0 and CPU quota
200%. All 969 pinned source/output entries passed before and after v3;
`PROVENANCE_UNCHANGED=true` is recorded after the terminal Lean exit.

The parent ran v1/v2. This agent ran only the authorized focused v3 via
Tailscale `100.108.41.90`, after checking that no compiler scope was active
and about 49.96 GB of RAM was available. Existing host swap usage was not
attributed to the new job, whose cgroup prohibited swap and whose measured
swap count was zero. The compiler slot was explicitly released at terminal
completion; evidence copies are complete and verified locally.

V3 source parent: `4066f0665dd1e6e89a848d9ba648f97fb11ef54d`.
The unchanged inherited overlay pin is
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, with borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. These are cache provenance,
not a claim that the new source was present in the older commits.

Exact SHA-256 evidence:

- Green source and v3 snapshot:
  `e386342223f1e32419104ce62c2d5e367d8cbf64129c572bc10b31d37d92fa2c`.
- Green `.olean`:
  `19c91eed8d23af13ec62fd5240b647c9a20e50c1ee1c8260f29103fa2c55aee0`.
- V3 manifest:
  `f47128148125d02eb1f11712a6e965ebfba59d370a436d25d8c400956e4900f2`.
- V3 log:
  `f72264431efdf42b31d5e0c89bd9a63ebfa1077f994df41ef7c3b5fcee237eab`.
- V2 snapshot:
  `7ff5d67c9cc52073d0e0d378bcd31111973dae156ff0bea0a4c1317c95a8f37e`.
- V2 manifest:
  `c24cd62bebc60ecedfb89d847cc63ddaa55d2dcbb7766c34e3d69d6ebc642043`.
- V2 log:
  `9e75bc89fd354c7487fe3b34b859df1f20806530f30b36f939487f532eeef769`.
- V1 snapshot:
  `ce5de3145f32359e9e501e7300fc60fa4cecc7add6162982241f404949c79a5f`.
- V1 manifest:
  `92d4f88d8d8d9ba5e96b839de900afb804d94076a2faa2626d43d1274022e56f`.
- V1 log:
  `8d237eec21e4dedb36ef1cae056411879a8d7baa025803e7ad8e7a47e86ffe1c`.
- Frozen runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

All attempt triplets use the prefix
`experiments/selected-regular-low-probability-nuc-v{1,2,3}` with suffixes
`-source.txt`, `-manifest.json` and `.log`. The ignored green `.olean` was
copied and hash-checked; source, snapshots, runner, logs and manifests are
the reproducible evidence rather than a required platform binary.
