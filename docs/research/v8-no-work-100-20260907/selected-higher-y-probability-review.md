# Selected higher-Y probability: checked source composition

[SelectedHigherYProbability.lean](experiments/SelectedHigherYProbability.lean)
is GREEN on focused NUC v1: exit 0, 3.30 seconds, peak RSS 6,879,988 KiB,
zero swaps and six standard-only axiom audits. It imports only the frozen
green `SelectedRegularLowProbability`. No other source, unrelated untracked
work or frozen review was edited. Source parent:
`354fbc6e298054057a8303e7e79c9a2560ffc0a5`. Source and evidence are frozen.

## Exact same-suffix partition

`highProbability` and `higherProbability` use the same gamma/kappa/tau/alpha
means and actual `suffix` as the existing `lowProbability`. The selected
final remains `(e.strategy gamma kappa).final tau alpha`.

`prefix_disjoint`, `pointwise_partition`, and `probability_partition` use
the existing `higher_partition` and literal LowPrefix complement to prove

    higherProbability = highProbability + lowProbability.

This is a disjoint weighted partition, not a sum over potentially different
strategies, chosen representatives or overlapping high/low witnesses.

## High branch and combined endpoint

`high_prefix_indicator` maps the actual high witness into
`EarlyC1HigherYSupport.highHigherGammas` via `high_prefix_mem`. The suffix
on that gamma is bounded by the actual `CausalOrderedRelation.after_unit`.
Averaging the fixed gamma indicator and using `fixed_early_high_count`
therefore gives

    highProbability <= 117077 / |Gamma|.

Its necessary hypotheses are retained explicitly: a fixed early result
`earlyC1 e.c1 = some p`, checked data, nonempty A and G, valid query count,
and `forall gamma in Gamma, gamma != 0`. The last condition is required by
the three-helper cover and cannot be silently dropped for arbitrary Gamma.
The previously checked sparse/dense helper dichotomy already supplies one
uniform count; no new maximum or separate sparse charge is introduced.

`higher_probability_bound` combines that bound with the checked low bound:

    higherProbability <= (117077+117049)/|Gamma|
      + integratedBudget(q,Gamma,A) + q/|G| + 18/|A|.

It additionally retains the low theorem's circle/non-west conditions,
nonempty Gamma, `6752623450 <= Gamma.card`, q>0, q<=262144, and the explicit
outside branch of the full pre-OOD singular-product pair-root event.
Only LOW incurs the displayed shared suffix repair. The original Gamma
normalization is unchanged throughout; the early-C1 condition is an
assumption about the fixed received word, not conditioning a gamma draw.

## Scope

The source execution retains fixed early C1, the actual degree-two helper
curve, full degree-28 claim timing, and adaptive final selection. No chosen
component tuple, supplied Q, uniqueness across factors, received-word
polynomiality or new regularity premise is added here.

This bounds the actual higher-Y prefix class under its stated hypotheses.
It does not dispose of early-decoder failure, the pre-OOD pair-root branch,
other covered classes, or the sampler/ROM/Fiat--Shamir coupling. It is not
yet a global payment, extraction or full acceptance bound. Only this new
leaf was checked under the existing capped NUC runner; no additional cache
export or package replay was required.

## Focused verification

One attempt, no failure or retry. Preflight over Tailscale found no active
compiler/build scope and about 49.96 GB of RAM available. Lean 4.32.0 ran
with `-j1 -M9500`, depth 200 and 250000 heartbeats, cgroup MemoryHigh=8 GiB,
MemoryMax=10 GiB, MemorySwapMax=0 and CPU quota 200%. Its 971 pinned
source/output entries passed before and after the successful terminal
result; the log records `PROVENANCE_UNCHANGED=true`. The compiler slot was
released on completion, and all attempt artifacts were copied locally and
hash-verified. Existing host swap usage is not attributed to this job;
its cgroup prohibited swap and its measured swap count was zero.

All six audits—`prefix_disjoint`, `pointwise_partition`,
`probability_partition`, `high_prefix_indicator`, `high_probability_bound`
and `higher_probability_bound`—use only `propext`, `Classical.choice` and
`Quot.sound`. No new axiom, source-condition weakening or resource increase
was used to obtain the result.

Inherited cache pin: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
These are cache provenance, distinct from the new source parent above.

Exact SHA-256 evidence:

- Source and frozen attempt snapshot:
  `598cdd2f23f2e8276e7a9785936f4b627f9f5c1e39a9557b237325ffd41ddcfa`.
- Green `.olean`:
  `aac729362082eed82a123b8511b040765b5854441099fba368ee2b1a3b41393b`.
- Manifest:
  `80f976544857aba7f309c4ed087c00534b67a5ce75e6838d5262db9902c897b7`.
- Log:
  `8965921999798ef62ccc81966102ae8646d299b1f4a48c74719b9acb32d2430e`.
- Frozen runner:
  `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

The attempt triplet is retained under
`experiments/selected-higher-y-probability-nuc-v1` with `-source.txt`,
`-manifest.json` and `.log` suffixes. The ignored output `.olean` is a
verified local cache artifact; reproducible evidence is the frozen source,
runner, snapshots, logs and manifest rather than a required platform binary.
