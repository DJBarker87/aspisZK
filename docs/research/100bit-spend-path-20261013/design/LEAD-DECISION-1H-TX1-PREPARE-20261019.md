# Lead decision 1h: `tx1_prepare` (2026-10-19)

## Decision 1g outcome (2d38f0977)

The four authorized `#[inline(never)]` attributes are applied. They brought
`verifier::tx1` from 4,672 down to 4,288 bytes, still over the 4,096 limit.
Native gates pass without `prover`:
- codec 1,233;
- the ordered 583-call trace (349/234);
- checkpoint23.

Stage1 replays still fail with a stack access violation, and stage2 is never
reached. There is no valid CU delta. These attempts are merged as evidence.
**The branch source still does not run on SBF.**

## Decision 1h: approved as proposed

The proposal is `evidence/decision1g-tx1-prepare-proposal-20261018/proposal.json`
(patch sha256 `a712eb0a…`). The lead read the patch and the disassembly
attribution:
- `verify_observed` returns into a tx1 frame buffer at fp−0x9f0.
- A 1,527-byte `memcpy` (0x5f7) then copies the `Verified` result into a
  second area at fp−0xfe7 before `Prepared::new`.

The new private `#[inline(never)] fn tx1_prepare` moves the existing
`verify_observed` / Semantic mark / `Prepared::new` statements, unchanged,
into the helper. It returns only `(sem.claims, p)`, both boxes, so neither
large area remains in tx1's frame.

Drop order is preserved:
- The outer binding `_semantic_claims` (named, not `_`) keeps the claims box
  alive until tx1 returns.
- When `Prepared::new` fails, the helper-local `sem` drops, as the outer `sem`
  did before.
- `Verified` has no custom Drop.

There is no public-signature change, no new allocation and no clone.

Gates (all required, on the final source):
1. Codec 1,233, the ordered 583-call trace, checkpoint23, and the tx1
   failure/order/observer injections, each on a `not(prover)` build with its
   exact features recorded.
2. One release SBF build. The strict stack audit must show no oversized frame
   on any function reachable from stage1 `[3,10]` or stage2 ASQ8, including
   `tx1_prepare` itself. Unreachable oversized symbols are listed with
   justification.
3. The saved transfer and withdrawal stage1/stage2 replays pass. Report
   invoked-verifier CU against 1,342,725 / 1,226,423.
4. Re-extract and re-pin `tx1` and `tx1_prepare`, covering control-flow
   success and the claims-ownership boundary. The old tx1 proof body is not
   reused as unchanged.

If `tx1` or `tx1_prepare` still exceeds 4,096 bytes, stop and report with the
disassembly. Do not add further attributes or splits without a new decision.
