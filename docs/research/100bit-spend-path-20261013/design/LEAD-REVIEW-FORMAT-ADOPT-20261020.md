# Lead review: adoption of the compact binary-multiproof format (2026-10-20)

Reviewed: branch codex/r1-format-adopt-20261019 (WIP 0d64fd6d3 from the
stopped Claude agent, then Codex commits 9a71031d3, c8ea8dd49); evidence
`evidence/format-adopt-20261019/` (REPORT.md, cu.json, receipts/,
artifacts-sha256.txt, source-hashes.json, r1p-retry-gate.json). Criteria:
`PREREG-PROOF-SIZE-2-20261019.md` items 1, 3, 4, 5, 6 (item 2 is the bound
re-run, launched separately).

## Accepted: PASS on items 1, 3, 4, 5, 6

The default build is the fixed-length 57,607-byte format; the eight-way path
survives only behind `audit-eight-way`, guarded against program builds. All
six regenerated statements equal the saved ones byte for byte.

| Fixture | Stage 1 (Δ B1) | Settlement (Δ B1) |
|---|---:|---:|
| transfer-13 | 1,196,046 (−3,602) | 1,135,481 (+5,724) |
| transfer-255 | 1,198,152 (−1,415) | 1,166,524 (+5,458) |
| transfer-1023 | 1,192,314 (−7,373) | 1,166,269 (+5,295) |
| withdrawal-13 | 1,192,444 (−5,781) | 1,145,777 (+6,827) |
| withdrawal-255 | 1,192,575 (−5,689) | 1,175,735 (+5,212) |
| withdrawal-1023 | 1,194,056 (−4,330) | 1,173,313 (+3,050) |

Gates passed: codec 1,233 byte-identical, ordered trace, checkpoint tests,
Pool suites (four feature sets), strict stack audit, teeth, mutations,
double spend, P_R1 retrying prover 8/8 accepted and verified. Uploads: 17
(16 proof + 1 statement); driver chunk 3,767 bytes, wallet 3,763 because its
length field makes 3,767 serialise to 4,100 (recorded, acceptable).

Pins: verifier `8cf8d84e…` (1,405,680 bytes), Pool `121f3e29…` (unchanged
from B1); source revision 9a71031d3; toolchains in artifacts-sha256.txt.

## Noted

- The six fixtures' proof and public files are committed as data (≈58 KB
  each), as the V5 release commits its proof; acceptable, not ELF/binaries.
- The Rust simulator (`sim.rs`) no longer verifies (`Err(Parse)`): its tests
  are ignored with a citation of PROOF-SIZE-OBLIGATIONS item 5. Its rewrite
  to the binary layout is a follow-up.
- Two wallet-suite exceptions: a pre-existing known-answer failure reproduced
  at the base, and a durable-store test that passes in isolation.

## This is the source freeze (gap-map step 0)

The verifier source at 9a71031d3 (research tip after this merge) is the
frozen R1 verifier for the soundness re-pins and the stage-2 extraction.
Any later verifier change reopens the re-pins and the CU bound.
