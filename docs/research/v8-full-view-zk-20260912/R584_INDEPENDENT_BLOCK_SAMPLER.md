# R584: source sampler to independent block program

Canonical target `AspisV8R19/R584IndependentBlockSampler.lean` compiled on the pinned Lean 4.32 cached workspace. Source SHA256 `8c412bfcc92c734de86531a8f9b46950ac5d7b13f71731adbdb0cae9d0f5e56f`, source revision `9cec79766c6977ae93e2b2bc458532b9b6888611`, final run `1791087333208476000`. Exit 0, wall 1.45s, peak Lean-child RSS 3,271,344 KiB, swap 0. Caps: MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128; Lean `-j1 -M4500`. Seven complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound` or subsets. All seven exact focused attempts are preserved with source snapshots, full logs and receipts; failed draft reports are not relied on.

## Precise proved boundary

`limb_independent_block` and `limbs_independent_block` prove exact equality of expectations between the existing source-shaped sampler programs and a block-only program, for arbitrary budgets/limb counts and observers of result plus cached block/index. The source program retains its initial transcript state and every output/advance ask. Its advance answers are integrated out only because this observer deliberately ignores the returned transcript state and oracle-call trace. The block program preserves the shared cursor, cached block, each limb's eight-attempt budget, rejection exhaustion and stopping.

`challenge_independent_block` proves equality for every observer of the complete ordinary four-limb result, including failure, starting from every state. This uses the independent-answer interpreter: every reached source oracle call receives an independently uniform 32-byte answer. It is a joint challenge result law, not a multiplication of separately proved limb marginals. The intermediate limb laws retain the cached block/index needed to compose later limbs faithfully.

The source-program equality does not assume freshness. It does not assert that the actual memoized shared oracle has the independent-answer law: repeated addresses remain a separate comparison/loss obligation. No verifier or security parameter was changed; no CU benchmark or unchanged regression suite was rerun.

## First remaining proposition and limits

Prove the block-only challenge's structural four-block answer bound and couple its complete stopped execution to a uniform four-block tape, then apply R579/R578 to obtain the exact joint tuple mass. Establish the actual shared-oracle comparison with collision, history and adaptive retry/resource losses explicitly. The current native R569 checked-sampler execution bridge and complete callback chronology are separate obligations.

This milestone does not prove a final-state or full-oracle-view probability law, native hash failure/divergence correspondence, universal joint C1/H1/G compatibility, a full published-view simulator, extraction/soundness, or end-to-end privacy/security. R583 separately preserves the deterministic total-H full challenge oracle view; that theorem is not a justification of independently uniform actual blocks.

[Canonical source](lean/AspisV8R19/R584IndependentBlockSampler.lean) and [evidence](evidence/r584-independent-block-sampler/) contain the precise statements, all attempts, dependency pins and complete axiom output.
