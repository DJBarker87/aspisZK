# Query completion and the following challenge's law

This step connects the [first-read recovery component](QUERY-FIRST-READ-BRIDGE.md)
to the existing list-answer and background-sampling interfaces. It proves
the independent-answer law of the following single duplex round, with the
recovered query component completed from background answers.

## Reuse and exact scope

`QueryCompletionSupport` proves that completion depends only on absent
squeeze cells on the recovered path. Changing an answer outside the
computed `missing` list leaves recovery unchanged. The result applies to
the complete recovered result, including its query output and state.

`QueryDecoderAnswers.fromAnswers` uses the old `DQ.accFrom` zip/lookup
function. The old `DQ.accFrom_map` theorem and the new support lemma prove
that supplying `missing.map H` gives the same recovery as supplying `H`
directly. `QueryAnswersFirstRead.fromAnswers_correct` then reuses the
first-read bridge to identify that output with the actual query absorb
address and q22 result. It retains the original trace-consistency,
collision, read, and endpoint-byte premises; it does not require an
arbitrary answer function or a global missing-cell coherence assumption.

`QueryNextLaw.own` is a following single duplex round: ask its absorb
address, spawn its squeeze read, and ask its advance read. Its output
function splits the answer list at `missing.length`, using the earlier
part for query recovery and the new squeeze answer for the new challenge.

`QueryNextLaw.background_law` reuses `BSOk.blaw_split` and finite-mean
congruence to prove an exact equality:

```
law of (completed query, new challenge)
  = average over missing query answers
      (average over fresh squeeze and advance answers
        (completed query, sigma(squeeze), advance)).
```

`background_sampler_law` identifies the inner law with the existing
`FS2.Duplex.samp` law via `samp_mean`. It permits an arbitrary function that
builds a prefix from the recovered component. The meaning and correct
round number of that prefix are not premises silently discharged by this
equality; they remain integration work. `background_bound` reuses
`pmean_le`: a bound valid for every fixed background completion is also a
bound for the averaged law. It assumes the fixed-completion bound and
does not supply a new numerical estimate.

These statements hold even when arbitrary completion answers cause query
recovery to fail or return a different selected state. The equality with
the actual execution is supplied separately by `fromAnswers_correct` for
the actual oracle-answer list. No claim of independent sampling of actual
adversarial transcript answers is inferred from that deterministic equality.

## What remains

The new `blaw` calculation is an independent-answer law. To turn it into an
adversarial first-read bound, the decoder must satisfy the existing trace
following/injection obligations, including freshness, address distinctness,
and chronological order. This step does not prove those obligations.

The complete R1 instance also needs earlier-round records and canonical
message parsing, the public/C1 initialization hash, the opening-domain
transition hash, a valid prefix constructor, and the concrete D1/D2/D3
connections. Shared-oracle collision accounting, Rust/account refinement
and full privacy remain open. No 100-bit release claim follows from this
component alone.

## Verification

Six final focused targets passed on the pinned NUC. The combined
`R1QueryCompletionLawCheckpoint-b` ran in 1.36 seconds at 3,518,516 KiB
peak RSS, zero swap, under 4G/6G/0 high/max/swap cgroup caps. All twelve
axiom reports use only `propext`, `Classical.choice` and/or `Quot.sound`.

The source base is `617bf78f6f77c803defb65e8d5eea16babb387be`.
The [evidence bundle](evidence/lean-query-completion-law-20261014/README.md)
retains sources and resource receipts for every attempt, including failed
attempts, plus the final compiled objects. The first combined checkpoint
was launched before its changed dependency had compiled and failed on the
missing new declaration. The final checkpoint followed that dependency's
successful compile; this was not an unchanged broad regression.

No historical theorem, Rust verifier, challenge sampler, or numerical
security ledger was modified.
