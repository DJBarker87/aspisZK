# Native/model bridge status

TX1:168 OPEN. No composed-row credit. All retained assumptions and frozen
artifacts are unchanged; no shipped Rust source was modified.

- Frozen queries_from_pairs / scan / finish / query_words / block_rank bodies
  match the committed Query31 source snapshot byte for byte. Exact lines,
  compared text and hashes: NHB_SOURCE_CORRESPONDENCE.json.
- Native cursor/decode window: K030 PASS, K031 single copied-block byte0
  corruption FAIL. Arbitrary32-byte block and cursor0..8, including exhaustion.
  Native input/output relation is the same block/word cursor as the coherent
  query_words and list-loop interfaces, not an independent challenge array.
- Native membership contracts0..10: matched positives/controls, exact domains
  and source snapshots in per-scope receipts. Higher-domain attempts hit tool
  limits, never counted or stubbed. No verdict depends on Option<fn> or a
  writable static. No field multiplication is reached.
- Word/cursor/full-frame compound cuts K037..K040: tool limits. K039 stops
  before native contains, so a pure membership-only diagnosis is unsupported.
  The scalar body cut is pursued independently, joined to K030 at the SAME
  source for-loop candidate binder. Source body bytes remain exact.
- Lean chain: NHB_Membership, Association, WordTrace, BlockTrace, Sampler,
  Domains, FullFrame, Canonical, OuterState, Reference, Prefix and Inactive
  are focused checked interfaces. They consume the NGQ canonical decoder,
  list-loop/first-stop and full-Result laws; NGQ proofs are not duplicated.
  Per-scope audits print only standard axioms for successful modules.

The physical producer of NGQ_Cuts.Trace is not supplied by constructing a
model trace or choosing a successful output. Native complete local word/frame
association and chronological physical cut assembly are still required.
The final ledger delta must remain empty while that obligation is open.

Final-stage additions: K043/K044 stopped word; K046/K047 low-length word
composed from the closed local Bool contracts; K050/K051 exhausted block with
no post-word stop test; K053/K054 opaque-call-log word (conditional membership
value only). The length16 scalar-expected contract K055 has a matched failing
K056 control. All source snapshots remain per attempt. Final native case
coverage and all attempts are in NHB_MEMBERSHIP_CALLEES.json/NHB_RESULTS.json.
No conditional/local edge is promoted to an NDT composed row.
