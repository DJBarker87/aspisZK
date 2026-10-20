# Query31 fixed-step driver refactor candidate

This is a source-only candidate based on the frozen `research` source. It does
not change production and has not been run through Charon, Aeneas, Lean, or Rust
compilation.

The candidate replaces the two eight-iteration loops on this path with direct
steps. In `SemanticTranscript::queries_canonical_bytes`, the first squeeze
uses the absorbed state; each following squeeze uses the preceding advance.
Thus block 7 is generated after exactly seven advance transitions, and all
8 squeeze/advance pairs are still materialized before scanning. The original
row-31 absorb, digest tags, decoder call, error mapping, and final assignment
of the decoder-selected state are retained.

In `r0_transcript::queries_from_pairs`, the scanner visits block indices
0 through 7 in order. The first `scan == true` returns that block's advance
along with the unchanged `finish` result. If none of indices 0 through 6 stops,
index 7 is scanned and `advances[7]` is returned whether its scan result is
true or false. `QueryScan::scan` and `QueryScan::finish` are unchanged. The
candidate therefore preserves the extra scan that detects success reached at
the end of a block, as well as the 64-draw limit behavior.

## Smallest equivalence frontier

The source-level equivalence needed before using this candidate is two small
lemmas, preferably in one focused owner:

1. For any absorbed state and hash function, the eight explicit pair calls
   produce exactly the two arrays produced by the existing materialization
   loop (same tag-1/tag-2 call order and the same seven transitions before
   block 7).
2. For any initial scanner state and those arrays, the unrolled branch chain
   has the same final scanner state, `finish` result, and selected continuation
   as the loop: split on the first index whose `scan` returns true, or the
   no-stop case. Do not replace the decoder's selected continuation with
   `advances[7]`; that equality is only the no-stop/default behavior of this
   source routine, not a general decoder contract.

The existing `Query31SourceCalls.queries_success_with_digest_pairs_full` and
`Query31MathematicalSchedule.queries_success_on_querySampler_schedule` provide
the digest-pair/materialized-array schedule. The existing
`QueryScanActualScanBridge.queryscan_actual_success_q22` and
`QueryScanFiniteCorrespondence.queryscan_q22_finite_correspondence` provide
per-block scan behavior. `finish` remains the exact unchanged source call; a
focused success/error result lemma for that declaration is still needed if the
new outer theorem consumes its result explicitly.

See `candidate-manifest.json` for frozen source and candidate hashes. The two
`.patch` files are dry-run checked with `git apply --check`; no patch was
applied to the working tree.
