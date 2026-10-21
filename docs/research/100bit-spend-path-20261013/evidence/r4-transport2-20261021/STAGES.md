# R4 transport continuation

Base 54054b905; branch codex/cx-r4-transport2-20261021. Focused cached-object
proofs, not a coherent frozen release replay. No endpoint premise is removed.

## Stage 1: wide reference and source steps

The exact optimized long-division limb and carry limb pass Kani under,
respectively, remainder < P and canonical digit < P, addend <= 257.
The complete shipped add_small_base_p passes against an indexed reference,
including every output digit and the final carry. Library traversal checks
show the eight reverse mutable visits and eight from_fn callback positions.
All checks retain unwinding assertions and use the capped host scope.

R4Transport2WideReference composes the *actual extracted* qm31_div_pass eight
times, preserving the entire quotient array, and proves its low digits and
remaining positional value equal the byte-rank Lean model. It has no
pass-success hypothesis; byte-array decoding is an explicit input equality.
All three top theorem audits are standard, zero swaps. Attempts 1 and 2
failed on do-pattern reduction; attempt 3 changes the wrapper to projections
and passes. No unchanged failed source was retried.

The syntactic step checker identifies the identical divider in both optimized
and indexed reference loops. This is not a kernel theorem about Rust's
from_fn/iter_mut library implementations. A whole-helper compiler/extraction
join, including the final quotient-array debug assertions and the connection
of the indexed add reference to its existing extraction, remains explicit.

## Stage 2: scanner step, invariant and selected state

All 23 fixed-length source-step partitions pass (37.286 s total, peak
591908 KiB, zero swap). Each starts with arbitrary stored words, arbitrary
candidate and draws <= 64. The exact source step is checked against indexed
membership, guard, length/draw updates and every unchanged array cell.
This replaces the earlier whole-block timeout; no old failed job was rerun.

R4Transport2ScanComposition proves a complete single-step relation lifts to
an arbitrary-length scan, preserves the bounded/distinct invariant, and
proves the materialized-pair driver equals Q22.scanOut under its reached
8-word budget. The eight-pair specialization has no assumption that advances
are distinct or that the returned state is advance7. Four new theorem audits
are standard, zero swap. The driver theorem includes the stop-before-word
behavior and the extra block after success on the previous eighth word.

Kani and Lean are separate proof engines: scan_loop_refines states the exact
relation their embedding must supply. The source splice checker and all 23
Kani partitions are evidence for the source step, not a newly accepted Lean
axiom for generated IntoIter methods. The existing extraction's external
iterator implementation boundary is still not a kernel-checked theorem.

## Stage 3: prefix composition and caller obstruction

R4Transport2CirclePrefix threads the first-25 checkpoint state through both
actual retained circle block calls and the S2/P3 reseed. OpeningChain threads
that state through reached ordinary block calls, constructing length/label
bytes rather than asking for them anew. It permits the correct literal
row30 constructor via each call's explicit erase relation. These are sampler
prefixes; the theorem does not assert the row30 word is the frozen parsed word.

QueryPrefix identifies all sixteen actual source digest successes with the
model's eager eight-pair chain and the selected scan state. QueryAbsorb
discharges its absorb preimage from the actual source row31 absorb and
canonical message. QueryRho composes that query result with the actual row32
scalar_k call and its empty frame. Its hscan is the exact remaining relation
between the shipped scanner and the checked reference driver; the theorem
never replaces the selected state by advance7.

The exact row30 append cut passes Kani for arbitrary root32, round1[224]
and arbitrary selected byte: length256 and every byte is root || round1.
prefix-source.json pins the reached row25–32 expressions, opening reseed,
all eight eager source pairs and the selected state assignment. This is
source identity, not an extracted whole-verifier execution theorem.

CallerObstruction proves that PreparedModel.Boundaries can return arbitrary
query state and arbitrary inactive serialization. Thus success at this free
interface cannot establish either missing source fact. These are interface
countermodels, not implementation counterexamples. No premise was removed.

## Wide follow-up

AddReference composes the existing indexed carry extraction with positional
mod/div, with exact pinned reference source and object hashes. WideBounds
derives canonical digits and quotient+1 <=257 from the extracted eight-pass
reference and the input byte rank.

A new whole division-pass comparison times out at120s. The first attempt to
partition it into eight arithmetic+array roots also times out at120s total
(two roots finish, the next is interrupted). Neither job is accepted as a
passing batch or rerun. The replacement separates the already-passing scalar
divider contract from eight arbitrary-write iterator/address/frame contracts;
all eight pass in4.238s. This removes repeated nonlinear division from the
array-write proof. The exact iterator traversal and the extracted loop's
inductive theorem provide the composition structure. No cap is increased.
