# Successful replay to the actual alpha boundary

Status: focused deterministic source/Fiat--Shamir integration milestone. This
is not a global soundness or probability theorem.

## What is now constructed

`FSLivePrefixMiddleComponents.lean` eliminates a successful staged execution
into the exact `sourceThenGammaScript` run followed by the exact
`middleScript` run on its threaded oracle state. It also proves that a
successful authenticated suffix retains the dependent `out`, `gamma`, and
`middle` prefix; the suffix cannot replace those fields.

`SuccessfulReplayAlphaBoundary.lean` consumes one actual
`SuccessfulReplay`. Its root theorem constructs:

- the source/OOD/gamma result and intermediate digest;
- the source-functional middle result and intermediate digest;
- equality between that staged prefix and the prefix retained by the returned
  authenticated record;
- the literal `alphaBoundary` after response0 and the alpha nonce;
- the actual `candidateScript` result, equal to the alpha recorded by the
  replay; and
- the exact alpha candidate query in the resulting chronological oracle log.

The theorem does not accept a semantic program, alpha transcript, candidate
input, or coherence certificate from its caller.

`ExtractionCollectorActualAlphaFamily.lean` applies this constructor to all
29 x 4 cells of the existing verified-successful family. It does not strengthen
the still-supplied `CompleteMatrix` premise or prove common chronology.

`SuccessfulReplayAlphaDisposition.lean` then applies the target classifier at
an alpha boundary constructed from replay success. The result is total:

1. prior adversary Q1, with the exact fixed-record membership and driving-input
   equality needed by `constructLegalReplay`;
2. a prior table target; or
3. an absent target.

The last two alternatives remain visible and receive no probability here.

## Decisive remaining producer

The next theorem cannot merely reuse matrix labels. It must construct the
nested gamma/alpha replay schedule from one chronological random-oracle
execution. In particular:

- a requested programmed alpha target must equal the actual candidate input
  reconstructed above, or the mismatch must enter a precisely defined
  prior-target/late-target/full-output collision event;
- equal parsed alpha values do not imply equal candidate inputs;
- the start-only replay constructor can target only a query in the frozen
  adversary Q1, so a verifier-side query alone is not sufficient provenance;
- common kappa and tau values require a common chronological pre-alpha state,
  not merely distinct transcript labels; and
- `CompleteMatrix` membership does not construct any of these facts.

The reusable V7 adaptive exposure scheduler and target-hit machinery are the
appropriate next dependency. The V8 task is to instantiate them with the
literal source-derived gamma and alpha candidate inputs, while retaining
prior-table, absent, replay-failure, and resource-abort branches.

## Focused checks

All commands used Lean 4.32.0, `-j1`, and `-M7500`, with the pinned union cache
and the repository `AspisFormal` search path.

| Leaf | Exit | Wall | Maximum RSS reported by `/usr/bin/time -l` | Swap | Axioms |
|---|---:|---:|---:|---:|---|
| `FSLivePrefixMiddleComponents.lean` | 0 | 7.00 s | 5,607,424,000 B | 0 | `propext`, `Classical.choice`, `Quot.sound` |
| `SuccessfulReplayAlphaBoundary.lean` | 0 | 3.70 s | 5,618,565,120 B | 0 | same |
| `SuccessfulReplayAlphaDisposition.lean` | 0 | 19.73 s | 5,621,121,024 B | 0 | same |
| `ExtractionCollectorActualAlphaFamily.lean` | 0 | 3.45 s | 5,572,362,240 B | 0 | same |

The macOS tool also reported peak-memory-footprint values around 870 MiB; both
metrics are retained verbatim in the logs rather than reconciled here.

Evidence directory:
`results/v8-completion-fs-extraction-20260911/successful-replay-alpha-boundary-v1/`.

No `sorry` or new axiom is present in these retained results. No full manifest,
Rust build, SBF build, probability composition, or literal-source refinement
was run.

## Security implication

This closes the analysis-only-alpha-input seam for each already constructed
successful replay. It does not yet construct the replay matrix or bound its
failure probability. Global soundness bits therefore remain unset.

