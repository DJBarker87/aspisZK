# Actual higher-prefix high-support inclusion

Status: kernel checked on the first focused NUC attempt. New file:
[SelectedHigherYHighSupport.lean](experiments/SelectedHigherYHighSupport.lean).
It imports the checked early-C1 count and causal higher-Y classification;
it does not reprove or change the count. All seven audit declarations use
only `propext`, `Classical.choice` and `Quot.sound`.
Source parent: `2a49280b70f17a4539927d7c6fd3121c417f2d7e`.

## Exact event

`Witness e gamma kappa tau alpha Q` names precisely the existing
[SelectedHigherYBranch.higherPrefix](experiments/SelectedHigherYBranch.lean)
body: the SAME Q belongs to the literal quotient family, passes
`¬badAnchor (e.rows gamma) Q`, represents the actual
`(e.strategy gamma kappa).final tau alpha`, and has a retained higher-Y
factor root for its reconstructed original. `witness_exists_iff` is the
literal equivalence to that already checked prefix.

`HighSupport received Q` is exactly

    (fibreBad (exactInitialEncoder Q) received).card <= 4*15334.

These are complete quotient fibres of the actual selected virtual word,
not original symbols or component own-support coordinates. On 262144
fibres this means at least 200808 complete matches. No pole deletion or
renormalized domain is introduced here; the existing quotient-to-original
cover handles its own pole loss.

`HighPrefix` requires both `Witness` and `HighSupport` for ONE existential
Q. `high_prefix_mem` concludes

    gamma in EarlyC1HigherYSupport.highHigherGammas e.c1 e.c2 e.data Gamma

whenever gamma belongs to Gamma. `witness_image` derives both image
equations from the actual row-prefix badAnchor gate; no arbitrary row/data
correspondence is supplied. The root, factor, and support use that same Q.
The theorem requires no early-C1 success or Data.Checked premise because
this step only transports the event. Those premises remain necessary when
the existing count theorem is subsequently applied.

## Regular and singular consumers

`fixed_branch_high_prefix` takes the actual `Qualified` witness, its
badAnchor gate, its literal adaptive-final equality, the retained factor
membership/degree, and its high-support test. It constructs `HighPrefix`.
It ignores any derivative information, so the same construction applies
after either side of `qualifying_regular_or_singular`.

Importantly, `fixedRegularPrefix` itself does not encode prime-factor
membership, retention or Y-degree: its F is a parameter. Those facts must
come from the actual higher-factor classification, as the constructor's
explicit arguments record. A mere nonzero derivative is not substituted
for them. No Q, final, or support is frozen before alpha.

## Exact remainder, not an acceptance implication

`higher_partition` splits the existing higher event into `HighPrefix` or
`LowPrefix`, where the latter is `higherPrefix AND NOT HighPrefix`.
This is disjoint even if the same final has multiple quotient witnesses.
`low_witness_bad` proves that EVERY witness satisfying all the same higher
prefix gates then has more than 61336 bad fibres.

An existential low-support alternative would not produce this disjoint
partition: one prefix could have both a high and a low representative.
Nor may a high-support Q unrelated to the actual higher witness be spliced
into its image/root equations. Singular branches do not supply the regular
uniqueness theorem needed to justify such a replacement.

The precise missing implication is NOT image recovery inside higherPrefix:
that is already a consequence of badAnchor. It is stronger support.
[QuotientFamilySelected.mem_literalFamily](experiments/QuotientFamilySelected.lean)
guarantees only at least 9558 complete matches. It cannot be read as the
200808-match assertion. Likewise the 38230-original-symbol guarantee of
`qualified_support_38230` is on another coordinate set and is insufficient.

Terminal acceptance alone does not imply higherPrefix, image validity or
this support threshold. Existing no-good, factor-exception, linear and
quadratic reductions retain their respective accepted-mass alternatives.
Intersecting their genuine higher remainder with the new high event gives
the advertised inclusion; the low event and early-C1-none branch remain.
No new acceptance bound, gamma/query marginal product, source sampler law,
authentication theorem, or extraction/payment endpoint is claimed.

## Focused verification

The parent agent ran the serial Tailscale NUC check; this agent verified
the copied source snapshot, output, log and manifest locally. Attempt
[selected-higher-y-high-support-nuc-v1](experiments/selected-higher-y-high-support-nuc-v1.log)
exited 0 in 3.39 seconds, peak RSS 6864620 KiB, zero swaps. Both 953-entry
provenance checks passed unchanged. There were no failed attempts for this
target and no cold dependency or package replay.

Inherited cache pin: `289d7356c78a4cd493fe61a54f9548f2a0c11298`;
borrowed V7 source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
The command was `run_higher_y_nuc.sh TASK SelectedHigherYHighSupport
selected-higher-y-high-support-nuc-v1`, with TASK
`/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`. Lean 4.32.0 ran
`-j1 -M9500` under MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0 and
CPUQuota 200%. Source limits stayed depth 200 and 200000 heartbeats.

| Artifact | SHA-256 |
| --- | --- |
| Frozen source / v1 snapshot | `9450da8d1acbbfa31c5495abc7afa4bfc9a5937d1c8ad4b5bdc13e55ae816326` |
| Olean | `3dc3a0a65418fb5dba0a8441d511e6e9c7d254055cd893c37c91c4116427f2e1` |
| V1 manifest | `cace01e7f6ed9dabbfd9bdf17d4f78b396456e7abd7534333b21c2aad8846348` |
| V1 log | `749bbfbe7056309e1a70b9851ef96912780b04b0cebca34b4aaf20fdb0c3de8b` |
| Runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
