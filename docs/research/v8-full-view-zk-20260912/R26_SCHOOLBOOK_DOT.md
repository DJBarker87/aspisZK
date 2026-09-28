# R26: whole-dot schoolbook experiment rejected

2026-09-28. Parent and selected control:
`0319ac2b7b5483160f40a5df51bff0c1f403367e` (R25).
Research branch `research/v8-r26-schoolbook-dot-20260928` retains experiments
and evidence, **not a replacement for the faster R25 execution profile**.

| Complete unchanged verifier | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| R25 control | 1,637,329 | 1,638,823 | Keep |
| Sixteen array accumulators | 1,669,196 | 1,670,584 | Reject |
| Explicitly unrolled accumulation/reduction | 1,671,116 | 1,672,504 | Reject |
| Channel-at-a-time immutable passes | 1,980,821 | 1,982,209 | Reject |

Every actual 1M execution still exhausts. No supported-budget success is
claimed. All three candidates pass the two complete genuine proofs under the
diagnostic cap, 3,281 host wire controls (3,280 checked rejections), corrupted
final checked rejection under the diagnostic cap, and stack-safe SBF builds.
Same 256KiB heap and unchanged simulated accounts. No resource failure is
described as validation rejection. Protocol, proofs, T163, sparse G, transcript
and canonical parsing are unchanged; no production deployment or wallet work.

## Tested arithmetic and its boundary

Unlike R20's nine-channel Karatsuba whole-dot accumulator, this experiment
accumulates the sixteen schoolbook products used by R24's faster scalar
kernel, reconstructing the extension field only after the complete dot.
Every operand limb is checked. Length equality and the 4,096-term cap remain.
The channel-at-a-time variant validates all immutable operands before its pure
passes, including operands multiplied by zero; no stateful callback is reordered.

Four canonical products fit in u64. A single Mersenne fold after each block
is below 5P, and at most 1,024 blocks keep each partial sum below 2^44. Sixteen
unchanged general reducers produce canonical residues. Linear reconstruction
with nonnegative P offsets stays below 8P and is reduced to four output limbs.
No general reducer or public noncanonical fallback is weakened.

Every candidate compares against the retained R20 adapter on 576 vectors,
lengths 0 through 4,096 including maximal canonical limbs, 7,272 noncanonical
cases and two length errors. The retained small-dot caller checks also pass
600,192 comparisons. These are actual staged Rust executions, not the only
evidence for algebra and not proofs of arbitrary source behavior.

## Measured reason to reject the array layout

The complete array-candidate trace accepts at exactly **1,669,196 CU**, with
byte-identical `.text` checked against its unstripped symbol artifact. It
executes 1,562,353 instructions versus R25's 1,530,486. All **31,867 extra
instructions** are in the changed checked-dot function: 149,272 versus 117,405
exclusive instructions, still 65 entries. Across the trace there are 43,343
additional loads/stores and 12,163 fewer shifts. Fewer reductions do not imply
less executed work when the accumulator state increases memory traffic.

Register-entry evidence records the actual dot lengths: one length 4, 33
length 5, 17 length 6, four length 16, ten length 27 (605 product terms total).
This is not a workload dominated by long 4,096-term contractions. Explicit
unrolling and channel-major passes were measured independently; neither wins.
The large channel-major regression is recorded without inventing an
instruction-level diagnosis for that untraced variant.

## Focused Lean leaves

`tools/R26SchoolbookDot.lean` proves a generic commutative-ring schoolbook
tower identity, distribution of the first reconstruction expression over a
finite sum, and the numeric block/partial/reconstruction bounds.

Initial compile: exit 1, wall 1.45s, RSS 1,719,352 KiB, swap 0; missing
`Finset.mul_sum` import, with a failed declaration reported using `sorryAx`.
That is retained as failed evidence, not accepted proof.
Replacing the group-only import with `Mathlib.Algebra.BigOperators.Ring.Finset`
gives **exit 0, wall 1.58s, RSS 1,731,160 KiB, swap 0** in the existing cached
Lean 4.31 workspace. `#print axioms`: first two leaves use `propext` and
`Quot.sound`; numeric bounds additionally use `Classical.choice`; no `sorryAx`.
Exact source SHA, command and parent revision are retained in metadata.
These leaves are neither Rust/machine refinement nor privacy/soundness proofs.

## Source-locking, resources and next measured target

Each isolated full stage has 180 checked source pins. Stage with
`tools/stage_r26_schoolbook_dot.py`, starting from
`/home/dombarker/project-offloads/aspis-r20-reduction-array-20260928-a`.
The two alternatives use `--unroll` and `--lane-major`. Existing runner and
output directory names retain `r24`/`r25` for compatibility; manifests identify
the changed implementation exactly. The generator gained optional flags
between variants; retained source files and manifests are authoritative for
each executed variant.

Cached release/offline/locked jobs use scoped MemoryHigh/MemoryMax 5G/7G for
builds, 2G/3G for runtime and focused Lean, 1G/2G for trace analysis;
MemorySwapMax=0 and TasksMax=128 throughout. No uncapped or debug arithmetic
release gate. The Solana skill's source/stack/runtime checks governed selection:
passing tests and Lean did not override the measured full-verifier regressions.

The selected R25 control's separate multiplication-caller audit attributes
all 2,269 QM31 multiplication entries. Largest grouped callers are ordinary
terminal (575), semantic basis (250), ordinary tensor fill (224), ordinary
block scalar (154), preparation closure (145), and opening caller (118).
These counts are not additive to the containing CU intervals. They identify
the next place to seek actual operation sharing or source-proved sparsity,
rather than another unmeasured generic accumulator replacement. In particular,
inspect the scalar ordinary path's exact support before computing unused
tensor coordinates. No prospective saving is booked.

`evidence/r26-schoolbook-dot` retains source deltas, logs, receipts, the failed
and successful focused Lean runs, the full array trace metadata, actual dot
lengths and the R25 multiplication-caller map. Raw traces/ELFs remain on the
NUC; keys are excluded and retained securely. Audit compact artifacts with
`tools/check_r26_evidence.py`; no unchanged expensive replay is required.

## Security gate unchanged

The first remaining source proposition is still the actual 626-equation
G-image compatibility for every admissible source prefix and same-public
witness change, with any exceptional source event explicitly bounded.
Coherent pre-beta quotient extraction, shared-oracle laws, seed/commitment
correspondence, posterior retention, retries and publication remain separate
open obligations. See `R25_CHECKED_DOT.md` and the earlier security ledger.
Neither this rejected optimization nor the better R25 resource result closes
full privacy or soundness.
