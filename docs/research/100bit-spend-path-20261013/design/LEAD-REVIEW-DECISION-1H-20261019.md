# Lead review: Decision 1h result 91a8b893e (2026-10-19)

The production diff is exactly the approved `tx1_prepare` patch
(sha256 a712eb0a…). The lead read it against 30a6c06c4. All Decision 1h gates
pass (`evidence/decision1h-20261019/checkpoint-report.json`):

1. **Native gates, `not(prover)`:** codec 1,233; ordered 583 calls;
   checkpoint23; 1,256 injection cases.
2. **SBF:** one release build. The strict stack audit shows no oversized frame
   on any function reachable from stage1 `[3,10]` or stage2 ASQ8.
3. **Runtime:** the saved transfer and withdrawal fixtures pass both stages.
4. **Re-extraction:** five Lean targets, with 25 standard-or-empty axiom
   reports; re-pin diffs recorded.

**The branch source is runnable on SBF again.** This is the first passing
SBF runtime since the refactors that followed 8089cab8f.

Invoked verifier CU, with deltas against 1,342,725 / 1,226,423:

| Fixture | Stage 1 | Stage 2 |
|---|---:|---:|
| Transfer | 1,340,926 (−1,799) | 1,226,487 (+64) |
| Withdrawal | 1,339,433 (−3,292) | 1,226,213 (−210) |

Stage 1 is still above the 1.3M target (G_R1.1 open, about 40k over). The
Digest32 and extraction refactors (Decisions 1–1h) are now accepted as
release-candidate source, subject to the standing gates. The J1.R13 artifact
pin can be taken from this build's ELF hash, recorded in the report.
