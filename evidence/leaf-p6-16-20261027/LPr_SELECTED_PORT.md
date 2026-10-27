# Selected-byte/word ports, stage 3

LPr_SelectedBytes.selected (L014) proves success, length32 and EXACT drop/take
identity of the native selected range for the SAME928-byte input and lane<29.
It proves the actual wrapping-add/multiply indices equal their nonwrapping
natural indices, using the pinned platform width. These are exactly the
source iterator bounds, with no decoder-success or final-result hypothesis.

LPr_SelectedWords.window_word (L015) identifies the exact native
U32.from_le_bytes selected word with the global natural polynomial at
32*row+4*j. selected_words transports arbitrary global natural word bounds
into all actual slice/length/native-word bounds required by ByteDomain.
Definitions match LPq_BytesTotal.word / LPq_ExpandedWords.word definitionally;
that nominal LPq import/application is NOT compiled here, and is not credited.

New theorem domain is input length928, lane<29, word<8, plus natural canonical
word bounds for selected_words. Those last bounds MUST still be derived from
actual check_values/expand_values results. This helper does not assert callers
establish them. In particular it is NOT an alternative CLOSED leaf domain.

L013 rejected symbolic platform-size/length arithmetic; L014 replacement passes
exit0 wall1.428882112s RSS2649536KiB swap0. L015 passes exit0 wall1.432331035s
RSS2639356KiB swap0. All four roots standard-only axioms. Exact statements,
commands/source hashes/dependency fingerprints/revisions in the per-run receipts.
No native Rust or Kani replay needed for these pinned-library proofs. Reuse
LPq local gates without modification; no new stubs or strengthened caller claim.
