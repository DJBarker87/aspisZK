# op223 final handoff

Branch: codex/pv-op223-20261027. Base: 258c685f5083c19ac238cecc0ade75dc6499f4f6.
Applied implementation: 6be26e38fddd78c4a97027689ffa329e4a8e8038; later commits
change only proof, design, orchestration and evidence. FINAL-SOURCE-IDENTITY.json
confirms zero implementation diff and local/host hash equality.

Published: R1Z.PV_Op223_Source.op223_source (actual applied extraction),
R1Z.PV_Op223_Source.op223_p6 (requested selected-ops P6 equation),
R1Z.PV_Op223_Source.P_source_p6 (exact V164 premise), and
R1Z.PV_Op223_V164.refinement. Complete Result and arbitrary raw inputs are
preserved. V164 before: P_source_p6, reservation, P_proof_bytes; candidate after:
reservation, P_proof_bytes, with ops specialized only by installing extracted
op223. The historical arbitrary-dictionary theorem is unchanged. No T item is
added; no deployed privacy endpoint is claimed closed.

All default/devnet/Pool ELF pins match. Fixed transfer/withdrawal proof/public
bytes, returned observations and ledger bytes agree. Native release differential:
1000 fresh pairs (coins 2000–2999), 600 complete proofs, 100 rejected prefixes,
400 errors, four complete-oracle-log pairs. All pass; exit 0 / wall 12956.131 s /
process peak RSS 622236 KiB / swap 0. Aggregate peak 6444085248 bytes, pids peak
54, pids max events 0, OOM 0. Soft MemoryHigh events 1581; original caps retained.
The sole failed native build had missing tracked harness inputs; supplied exact
files, then successful new build. No disagreement or pin mismatch occurred.

Raw corpus deleted after retaining all text receipts and SHA256 manifest
(corpus-evidence/cleanup.json). Three SBF keys remain retained at mode 0600;
no keys deleted. No binaries or raw proofs/oracle streams committed.

Final audits 43597/43598/43599 exit 0, walls 1.788/1.798/1.836 s, process peak
RSS 4293240/4285512/4292364 KiB, swap 0. All printed axioms are a subset of
propext, Classical.choice, Quot.sound. Exact commands, source hashes, submission
revisions and dependency fingerprints are in the per-ID receipts and
PROOF-RECEIPTS.json. Host source_revision means applied Rust revision; the
separate lean_submission_revision and immutable snapshot identify Lean source.

Budget: 80/100 charged Lean attempts, 71 passes, nine failures; six uncharged
IDs 43300,43313,43328,43346,43354,43379. Kani 0. No unchanged regression was
repeated to spend the remaining 20 attempts after the requested candidate
premise and worker gates were complete. IDs 43383–43596 remain unused; the three
reserved audit IDs were used. No shared Env-J source or pinned extractor changed.

Next: lead schedules TIMING-PLAN.md with Stream A. Timing was not executed.
E1/E2, real RunJoin, P_proof_bytes, OS-failure independence, L1/L2/L3, endpoint
composition and final deployment closure remain substantive obligations.
Target not yet established.
