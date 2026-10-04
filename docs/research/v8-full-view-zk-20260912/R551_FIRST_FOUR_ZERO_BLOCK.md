# R551: one-block first-four zero mass

`R551FirstFourZeroBlockV10.lean` proves that, for one uniform 32-byte `State`,
the event that the first four 31-bit-masked words are zero has exact mass
`(1 / 2^31)^4`. The proof factors an abstract finite alphabet symbolically,
then specializes it using R421's uniform masked-word transport. It does not
prove the probability law of the full actual shared-oracle challenge, freshness
between oracle reads, or a security bound.

The canonical Lean source is
[`R551FirstFourZeroBlockV10.lean`](lean/AspisV8R19/R551FirstFourZeroBlockV10.lean).
Its SHA256 is `f99ee19cc9d3a471e1e9768a4bee2001a714e6d085f50885929bbaf1ee3ca2b6`.
The source revision was `1f8a1b24361584df351751fd4bae11f5690de448`; its direct
local import `R421UniformMasked31Block.lean` had SHA256
`631c8a5623e2aa42194fe45bf270b1a0f0ee90e3219c9be302fc4b15c45701b0`.

The changed focused target `AspisV8R19/R551FirstFourZeroBlockV10.lean` compiled
in the pinned cached workspace with exit status 0, wall time 1.69 seconds, peak
Lean-child RSS 3,249,316 KiB, and swap 0. The job used `-j1 -M4500` with
`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Complete
`#print axioms` output for all six named declarations is in the successful
focus log and receipt under
[`evidence/r551-first-four-zero-block`](evidence/r551-first-four-zero-block/).
Every declaration depends only on `propext`, `Classical.choice`, and
`Quot.sound`; none depends on `sorryAx`.

The evidence bundle preserves the original unverified draft, all failed
focused attempts, the isolated green split-equivalence predecessor, and the
successful final source, log, and receipt. The first remaining proposition is
the deterministic execution bridge: under this block event, show the selected
QM31 sampler accepts exactly four limbs without refill or failure, retains its
two oracle calls and advanced state, and returns the four zero limbs. Connecting
that model result to the selected transcript remains separate work.
