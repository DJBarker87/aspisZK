# Lead review: proof-size feasibility test (2026-10-19)

Reviewed: branch codex/r1-proof-size-20261019 (S1 6c753caba, S2 f9710f598,
S3 ab0b4b76c, S4 866cbdc33), evidence `evidence/proof-size-20261019/`,
obligations `design/PROOF-SIZE-OBLIGATIONS-20261019.md`. Criteria:
`PREREG-PROOF-SIZE-20261019.md`, unchanged.

## Verdict: NOT VIABLE, as pre-registered

Criterion 2 (no CU increase on any fixture) fails on Pool settlement for five
of six fixtures, by +4,127 to +9,919 CU. All other criteria pass.

| Measurement | Result |
|---|---|
| Size (fixed length, padded to the 914-node worst case) | **57,607 bytes** on every fixture; bound attained by bit-reversed index sets; 20,000 random query sets max 903 nodes |
| Stage-1 CU vs B1 | −100 to −4,868 on all six (under) |
| Settlement CU vs B1 | −2,148 (transfer-13); +4,127 to +9,919 on the other five |
| Parameters | 22 queries, two folds, final 64, salts, wide values unchanged; shipped default ELF byte-identical to 4421aafd… |
| Teeth | all reject (wrong sibling, missing/extra node, duplicate/misordered leaf, non-zero padding, injected high half, checkpoint over expanded bytes) |
| Uploads (measured 329-byte TxV1 overhead → 3,767-byte chunk) | shipped 34 → candidate **16** at the TxV1 maximum; 139 → 65 at today's 900-byte driver chunk |

Where the CU goes: hashing the shorter proof saves 33k per transaction, as
proposed; the binary multiproofs cost +20–25k (stage 1) and +34–38k (stage
2) because there are 2.5× as many parent hashes and each carries program
overhead the syscall-only estimate omitted. Three candidate versions were
measured, each a source change; the first was +86–92k / +33–38k.

## Reading

The criterion that failed is the conservative one. Stage 1, the transaction
with 16k of margin under the worst-case bound, got cheaper. Settlement, which
has 87–100k of margin (`LEAD-REVIEW-CU-BOUND-2-20261019.md`), rose by at most
10k. The pre-registered line was "no increase", so the verdict stands as
FAIL; whether a ≤10k settlement increase is acceptable in exchange for a
57.6 KB proof (16 uploads instead of 34) is a user decision, to be taken as a
new pre-registration, not a reinterpretation of this one.

## Facts that bear on that decision

1. The upload halving needs the wallet's chunk size raised to fill a TxV1
   transaction (3,767 bytes). That change alone takes the shipped proof from
   139 uploads to 34. It is independent of the format.
2. Obligations (`PROOF-SIZE-OBLIGATIONS-20261019.md`): source refinement of
   the candidate verifier (L); binary commitment binding and collision
   targets (M); extractor word recovery and the Merkle compiler (M); privacy
   layout and the Rust simulator (M); read-count constants and the binary
   node domain tag (S). None started.
3. The privacy read budget breaks: `mc_le` in `R1Z/CommitReadsR1.lean`
   (115 + Mc ≤ 2^21) is false for binary trees (Mc 2,359,296 + expander =
   2,457,715). The D41 budget constant and the error terms built on it must
   be re-derived; ε_hit has ample slack (2^-167) so the number is expected to
   survive, but it is a re-proof.
4. Not done: the P_R1 retry path on the candidate; the worst-case CU bound
   on the candidate.

## If the user proceeds

New pre-registration: settlement may rise by at most X per fixture (user
sets X ≤ 10k from this evidence) and the second-method CU bound must be
re-run on the candidate with both bounds ≤ 1.3M; the source freeze (gap-map
step 0) is then taken on the candidate.
