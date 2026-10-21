# Prover commitment continuation 11 — 2026-10-21

Branch `codex/cx-prover-commit11-20261021`, base `8e4931b1f`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit11-20261021/`.

Work in progress. No CallerLaw deletion or shipped execution certificate is claimed.

## Stage 1: byte loads and global cache

`ProverCommitOwnedBytes.readBlock_byteWord` identifies the exact extracted
four-byte load. `ProverCommitOwnedByteValue.fromLEBytes_value` proves the
little-endian numeric identity by induction on the byte list; `blockW_value`
and `byteWord_answer` identify it with the existing finite word equivalence.
No allocated stream or large numeral is evaluated.

`ProverCommitOwnedCache.next_cache` proves that each successful next-word call
preserves the identity of the cached block with the preceding answer from
the same finite oracle, and returns precisely the `wordsE` word at the current
position. Initial cache validity is unconditional. This proof includes the
refill and cached cases and retains the existing counter-capacity bound.

Accepted focused targets: J8329 (byte loads), J8332 (byte values), J8335
(cache and stream correspondence). Each exits 0, zero swaps, with only the
standard three axioms. Exact targets, source hashes, dependency fingerprints,
source revision, walls, peak RSS and all axioms/errors are in `lean/` receipts.
Drafts J8327–8328, J8330–8331, J8333–8334 are excluded elaboration failures,
not memory failures. No resource cap or recursion/heartbeat option is raised.
Only new worker-owned module/objects are installed in Env J; overwritten
versions of those modules/objects are snapshotted under this branch's host
workspace. No peer-owned source is changed.

## Stage 2: complete reference CallerLaw

`ProverCommitOwnedSequence` erases only the operational error/state wrapper
and proves that the exact extracted collector obeys the consuming word-loop
recurrence. `ProverCommitOwnedModel.sequence_model` proves equality with
`decodeWords` by induction on remaining words, using Stage 1's exact cache
law and the explicit retry budget. Both rejection and early acceptance
preserve the same suffix of one global finite oracle.

`ProverCommitOwnedArrayLaw.samples_array` transports the resulting list
equation to the actual finite arrays, proving lookup correspondence rather
than treating a default value as a sampled coordinate.
`ProverCommitOwnedCallerLaw.rawArrays_model` composes the two protocol-sized
streams. `quotient_decoder` gives the exact quotient equation, with the
identity coordinate equivalence. `ProverCommitOwnedEndpoint.caller_law`
constructs CallerLaw for precisely the fixed operational-reference prover
of `PrivacyR1HeadlineOwned`, with no new hypothesis.

Accepted focused attempts J8337, J8340, J8343, J8344, J8348 all exit 0,
zero swaps, standard axioms. Their thirteen new theorem audits are recorded
in the receipts. Excluded drafts have changed-source replacements; none
failed from memory pressure. No shipped Rust source or ELF input changes.

**Scope:** the mathematical CallerLaw for the fixed decoder is now proved.
This does not construct either shipped execution join, certify the actual
outer material-building loops, or prove all-family shipped callback coverage.
The existing headline is deliberately unchanged until those source gates
are addressed.

## Stage 3: bounded proof windows and premise deletion

`ProverCommitOwnedWindow.scalarFinite_window` proves that the operational
scalar computation depends only on the retained global answers at refill
positions inside its remaining word interval. `scalar_window` applies this
to all sixteen tries. `scalar_block_window` bounds that interval by three
aligned blocks. This is a restriction of one global oracle, not a fresh
independent ROM at each call. It gives the support condition a local Kani
window must satisfy; it does not assert that a shipped outer caller has
already supplied that condition. J8349 checks the three support lemmas;
J8350 adds the block-count bound. Both pass, standard axioms, zero swaps.

`PrivacyR1HeadlineOwnedClosed.privacy_headline_owned_closed` applies the
proved reference CallerLaw to the same D112 specialization. All other
premises, games, simulator, error and < 2^-100 conclusion are unchanged.
The original endpoint remains available. J8351 passes both audits (the
private CallerLaw application and the new headline), standard axioms,
zero swaps. It does not certify either retained shipped execution join.

The complete verbatim endpoint texts are `headline-before.lean.txt` and
`headline-after.lean.txt`; `headline-deletions.diff` contains precisely two
deleted lines and no additions. Both texts share the separately proved
CallerLaw application, so the theorem body is literally unchanged.

Verbatim before (declaration prefix):

```lean
theorem privacy_headline_owned_closed
    (builder_premises : BuilderPremises h B x)
    (R_commit_caller : ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

Verbatim after (declaration prefix):

```lean
theorem privacy_headline_owned_closed
    (builder_premises : BuilderPremises h B x)
    (observer_program : (source).Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
```

The argument name in the unchanged proof resolves to the checked private
theorem, rather than to a caller-supplied hypothesis. This is a deletion
at the fixed operational-reference endpoint; no whole-shipped-execution
certificate follows from this deletion alone.

## Stage 4: canonical global-to-local rebasing

`ProverCommitOwnedRebase.windowAnswers` constructs each nine-answer local
table as a restriction of the retained global answers. `windowHash_at` proves
the callback identity at every in-range request. `window_wrapping_offset`
proves that the Rust local-ROM wrapping subtraction is ordinary subtraction
inside these windows. `scalar_rebase` removes the support premise from
Stage 3 by constructing the correct local backend. `scalar_window_offset`
places the current counter at offset zero or one, inside the scalar contract
margin. Global allocation and counter bounds exclude wraparound.

`ProverCommitOwnedWindowCollection.collect_rebase` then proves the complete
collection equals per-scalar rebased calls, by symbolic induction, including
partial Rust error states. Each call uses a bounded local backend; every
window is derived from the same global input. No full array is supplied to a
nine-block ROM. No fresh independent table is substituted for a retained
global answer. J8352 checks the initial three rebasing lemmas, J8353 the
final four, J8354 the collection induction: all exit 0, standard axioms,
zero swaps. Source identities, dependencies and resource fields are in
the verbatim receipts.

This is the mathematical rebasing bridge for the P6 route. It does not
itself prove the actual material builder's loop schedule, entry-point
transport, or all-family shipped callback coverage.
