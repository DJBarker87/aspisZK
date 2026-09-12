# Verification of the body returned by a legal replay

Status: checked same-body source milestone; matrix collection, extraction and
global Fiat--Shamir soundness remain open.

## Corrected replay architecture

`lean/ExtractionCollectorVerifiedBodySource.lean` separates two operations
that the earlier replayable-source shell conflated:

1. a same-tape adversary replay runs and returns a submitted proof body; and
2. the selected functional verifier runs on that returned body, beginning at
   the replay's resulting shared-oracle state with actor `.verifier`.

`verifiedSourceAttempt` retains legal-replay failure, verifier oracle abort,
verifier fuel exhaustion, verifier rejection and verifier resource failure as
separate outcomes.  It creates a checked outcome only after the verifier
returns normally and its result checker accepts that returned result.

The selected specialization runs the source-shaped functional
`wholeStagedScript` on the replay-returned bytes.  Its dependent result stores
the body used to index the parsed record.  The checked theorem
`selected_attempt_checked_same_body` proves:

```text
checked selected replay attempt
  -> accepted dependent record body = legal replay's returned body.
```

The proof uses a structural `OracleMachine` map theorem and the actual
`runMachine` result.  It does not accept body equality, successful verification
or a semantic program as a premise.

The stronger
`selected_attempt_checked_constructs_functional_run` exposes the underlying
successful run of the unmodified `wholeStagedScript` on those same bytes.  It
is therefore more than a result tag: the checked outcome constructs an
operational replay, its returned bytes, and a normally returning functional
script run on those bytes.

The functional rerun begins with the replay-final oracle state and an explicit
`initialDigest`.  This leaf does not yet prove that the supplied digest is the
digest represented by that oracle state.  The precise result is consequently
same-body provenance for a checked functional rerun, not yet a
digest-continuous chronological continuation of the adversary execution.

## What remains

This is a one-attempt theorem.  It does not yet construct the 29-by-4 list of
attempts/configurations, preserve each checked attempt's provenance through
`CompleteMatrix`, or prove that four programmed alpha attempts share the
canonical pre-alpha boundary.  Those are the next source/extractor tasks.

`wholeStagedScript` includes the current source-shaped transcript and Merkle
suffix but not the complete terminal Boolean.  Therefore this result is not
complete selected-verifier acceptance, fold correctness, `SuccessfulAt`, a
payment witness, or a probability theorem.  Literal Rust refinement remains
outside the functional endpoint.

## Focused evidence

Lean 4.32.0, pinned union cache, `-j1 -M7500`:

- exit code: 0;
- wall time: 4.48 seconds;
- peak RSS reported by `/usr/bin/time -l`: 5,829,836,800 bytes;
- swaps: 0;
- printed axioms: `propext`, `Classical.choice`, `Quot.sound` only.

Source SHA-256:
`f0f076b6ddd9960cd3237d597bbb65d9bb4535fe202eb09e61df71f59392941f`.

Olean SHA-256:
`f2ace3c6c8417348b8f838d1bfdfdbeb30a4ca7cd17ad56a9cc166c88fe3360b`.

This was a cached focused check, not a clean first-party dependency replay.
The log and machine-readable evidence are under
`results/v8-completion-fs-extraction-20260911/replay-returned-body-v1/`.

## Security implication

The stale-body/supplied-program finding is closed for one functional replay
attempt: the verifier result and constructed functional run use the exact
adversary-returned body.
No global accepted-but-unextracted probability is reduced yet because the
attempt collector, terminal acceptance and extraction implications remain
unproved.  Global security bits remain unset and grinding contributes zero.
