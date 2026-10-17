# Lead review: Prepared/tx1 checkpoint 0189f1094 (2026-10-17)

Merged onto 9e0bde53e, not fast-forwarded. No path is touched by both sides.
The lead diffed production source against 3da1531fc. Only `verifier.rs`
changed, and the change is exactly the Decision 1b patch
(`prepared_claim`, owned `(alpha,row)`) plus the Decision 1c patch
(`tx1_finish`). There is no `inline` attribute and no other edit.

## Accepted

- **Decision 1b/1c gates passed on the final source:**
  - codec 1,233 byte-identical;
  - 583 ordered calls identical (349/234);
  - 23 checkpoint tests pass;
  - Prepared injections: 528 cases (all 174 `dot.push` positions,
    S1/S2/D, query boundary);
  - tx1 injections: 5 on the real saved S2 proof, plus 30 on the shared
    S1/S2/D suite.

  The shared suite is a control-flow differential on synthetic interfaces,
  as the report states. It does not cover observer-absent runs.
- **Reachability.** Actual `tx1` success reaches semantic-verifier success
  and `Prepared::new` success. This removes the universal tx1 continuation.
  `prepare_success` derives the ordered opening calls 27..32 (27..31 on S1)
  and links their states. Query sampling and the claim arithmetic remain
  explicit boundary functions. There are 18 + 1 standard-only axiom
  reports.
- **The C2 design note** is accepted as the plan:
  - an owned execution witness for known-host runs;
  - the recorded-experiment cut compiler for arbitrary accepted proofs.

  Its separate obligations (packing, salt/path, source/oracle, custody,
  checkpoint, context) are kept as listed. Proof work may begin.
- **Re-pin addendum:** 289 unchanged, 52 re-extracted, 1 authorized
  replacement, 0 unresolved. The final cone review stays at J1.R13.

## Decision 1d: `verify_finish` approved

`verify-prefix-proposal-kit/proposal/proposal.patch`, reviewed by the lead:
- The post-`begin` semantic tail moves unchanged into `verify_finish`, which
  takes owned `Public` (which is `Copy`), `Prefix`, `Transcript`,
  `Challenges` and `Observer`.
- The non-capturing nested `mark` is lifted to module scope. No other `mark`
  exists in `r1_semantic.rs`.

Same gates as 1c, with injections at Prefix parse, `public_transcript` and
`begin`, and at the first and last semantic rows of the tail.

## Decision 1e: eight-pair unroll in `Transcript::queries` approved

`opening-queries-extraction-kit/proposal-eight-pairs/proposal.patch` writes
out the `0..8` loop as eight pairs of `digest(state,[1])`/`digest(state,[2])`
in the same order with the same state threading. Nothing else in the method
changes. Same gates. Its injection must fail each of the 16 digest positions
and `queries_from_pairs`.

## Decision 1f: standing authorization for extraction refactors

To avoid one approval round per extractor blocker, workers may apply the
following without a new decision. Each one still needs the full gate set
before it counts, and the lead reviews each diff at the checkpoint.

**Permitted:**
1. Moving an unchanged statement sequence into a private helper, with owned
   or borrowed arguments.
2. Unrolling a loop whose bound is a compile-time constant of at most 32,
   keeping call order and state threading.
3. Lifting a non-capturing nested `fn` to module scope.
4. Returning a tuple from a branch instead of mutating an outer binding,
   when the values are identical on every path.

**Not covered; these need a proposal:**
- any change to arithmetic, types, error variants, or the order of hash,
  sampler or trace calls;
- any `inline`/`cold` attribute;
- any change to `aspis-core` or the programs crates;
- any data-dependent loop;
- anything that changes a public signature.

**Gates for every change:**
- codec 1,233;
- the ordered counter trace;
- the 23 checkpoint tests;
- injections at every moved failure point;
- a reverse-patch audit;
- a listing in the next checkpoint report.

SBF stack and code-size effects are checked once at J1.R13. If they fail,
the lead decides there.

## Open

- Semantic rows 15..24.
- Circle rows 25/26 and reaching the reseed at row 26.
- The rest of the opening query implementation (the trace `enumerate`
  loop) and the whole 33-row carry.
- The full25 transcript byte identity.
- `hread` and `htyped`/`ha`.
- Digest32/table/init correspondence.
- C1/C2 constructors and custody.
