# R591: complete block execution

R591 connects deterministic indexed replies to complete ordinary four-limb block execution through the R572 sequential word evaluator. It preserves every rejection, failure, stopping result, cached block, and consumed reply counter.

## Verification

- Canonical source: `lean/AspisV8R19/R591CompleteBlockExecution.lean`
- Original draft: `.r21-scratch/R591CompleteBlockExecution.UNVERIFIED.lean`
- Canonical/draft SHA256: `54fe13227133809b017b3189aa67316a77b0de92b243d5bcd24dc38e7a9d42c3` (byte-identical)
- Canonical target receipt: `1791088371045472000`
- Source revision: `93b14c2102aefc0418fdbfb93f06c3590bd39c72`
- Result: exit 0; wall 1.33 s; Lean-child peak RSS 3,262,920 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Four complete final `#print axioms` reports use only subsets of `[propext, Classical.choice, Quot.sound]`.

The compiled source, log, receipt, direct source pins, runner, explicit publish paths, and recursive SHA manifest are retained in `evidence/r591-complete-block-execution/`. No check was rerun for this promotion.

## Boundary

R591 is deterministic indexed-reply execution through complete ordinary four-limb block sampling. It does not prove an actual shared-oracle independent law, a native wrapper or full callback correspondence, privacy, or security.

The first remaining step is a finite four-block tape pointwise bridge and law transfer using existing `Within 4`, `mean_evalTape`, and R579; then actual shared-oracle losses.
