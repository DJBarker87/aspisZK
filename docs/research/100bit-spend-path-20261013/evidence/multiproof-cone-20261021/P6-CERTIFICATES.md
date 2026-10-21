# Composed P6 certificates — pass 2

Pass 2 supersedes the pass-1 whole-function solver blocker below. The
whole-function certificate is the composition of the already verified local
cuts, kernel node/level/height inductions, and callback/leaf contracts. No
whole-function Kani harness is run in this pass.

The new additive targets are `MultiproofConeP6Composition`,
`MultiproofConeP6Verify`, `MultiproofConeP6Batch`,
`MultiproofConeP6Callbacks`, and `MultiproofConeP6Frozen2Stage`.
The final checked statements and validation receipt summary follow below;
the historical failed solver attempts are retained verbatim for provenance.

## Precise retained boundary

The source denotation is the frozen binary control schedule at the named
P6 source/library lowering boundary. It is not a new Charon extraction of
the shipped functions. The boundary identifies physical/window rebasing,
checked array/slice/scalar operations, node/height-loop factoring, the
valid-index and final-root guards, packed-key/sorted-opening adapters,
count, and whole-word padding with the pinned certified cuts. Callback
and leaf effects are explicit local propositions in `P6Boundary`, never
axioms or assumed whole-function conclusions. Kani receipts remain
external P6 certificates, not kernel proof terms.

S2/S10 must still identify the reached source proof/query/root/key carriers
and enclosing TX1/Pool TX2 call trees with this denotation. The six exact
slot-view equations are the caller interface; `slot_bound` derives the
5504-byte bound from them. No separate size or successful-intermediate
execution premise is added to `both_batches`. This is scoped P6 stage
composition, not a global `AcceptedRunJoin` inhabitant or a release claim.

## Current checked endpoints

`MultiproofConeP6Frozen2Stage.function_certificates` proves both complete
function certificates from the local P6 boundary:

- `verify_in_place_owned`: the full source-loop/wrapper denotation equals
  generated `reference.verify_owned` for **every** arbitrary root, initial
  scratch (including n=0 or n>16), and physical byte slice of length ≤5504.
  Arity is Two and height is 18. No acceptance/sortedness hypothesis is
  added. Every Result, short rejection and partial scratch is retained.
- `batch_tree_owned`: complete ordered observations and scratch equal
  `MultiproofConeSlotState.slotState` for every Parsed/query/batch/kind input,
  arbitrary initial scratch and physical slot length ≤5504. The owned batch
  is instrumented composition of extracted `leaf_step`, physical levels and
  previously proved count/padding/root guards; it is **not** described as a
  generated extraction of the entire Rust batch function.

`P6Callbacks.three_parents` consumes each of binary/occupied/sibling's exact
one-call address and arbitrary returned digest at the checked write
continuation. `node_gate` derives the physical node equation for the occupied
and supplied branches. `P6Composition.rows_eq` and `levels_eq` induct over
reached nodes and levels, deriving every required next-state domain from
`binary_step_progress` / `level_preserve`. `eighteen_owned` uses the existing
extracted-level recurrence bridge. There is no successful-height hypothesis.
`P6Batch.leaves_eq` composes the single-leaf hash/dedup contract, derives the
capacity bound and retains immediate unequal-duplicate rejection. Its
physical tail consumes the node composition before the root comparison.

`MultiproofConeP6Frozen2Stage.sourceBatch_eq` substitutes those **proved**
function certificates through the actual scratch-threaded short-circuit.
`both_batches` then instantiates the inherited
`MultiproofConeFrozen2Stage.both_batches` for batch0 and batch1 separately.
Only P6Boundary and the six caller slot views remain; acceptance is the
antecedent of the accepted-run conclusion. No per-slot/level/batch equality
is hidden in P6Boundary. No successful leaf, duplicate consistency, count,
padding, root, invariant or successful intermediate Result is assumed.
Initial scratch suffixes are arbitrary and carried between slots.

Before: the prior review required a separate successful whole-verifier
solver comparison before stage instantiation. After: the complete bounded
function correspondence is a kernel composition of local contracts, and
the named frozen2 stage is instantiated from it. Quantifiers and the
accepted observation/Bool conclusion are preserved. The old failed
`source_row` contract is never used as a verified stub. All 288 possible
parent answers remain independent; the actual oracle reply at each ask is
written before later reads. No zero-filled physical buffer or repeated
constant answer replaces the source input.

## Focused validation and exact resource evidence

| Exact Lean target (`lean/`) | Attempt | Exit | Wall seconds | Peak RSS bytes | Swap | Source revision |
|---|---:|---:|---:|---:|---:|---|
| `MultiproofConeP6Composition.lean` | 1 | 0 | 15.452180 | 3627679744 | 0 | `3af931da4e590aea7748f6e45a26550a1b099f08` |
| `MultiproofConeP6Verify.lean` | 2 | 0 | 12.748723 | 3629334528 | 0 | `6e23ed9f0ac0c0d29122f38cf64be67c97447faa` |
| `MultiproofConeP6Batch.lean` | 2 | 0 | 13.254556 | 3630104576 | 0 | `6e23ed9f0ac0c0d29122f38cf64be67c97447faa` |
| `MultiproofConeP6Callbacks.lean` | 1 | 0 | 24.647157 | 3619176448 | 0 | `67ea4d933f433ffe4c1b9c6a8146228d306e0ec8` |
| `MultiproofConeP6Frozen2Stage.lean` | 4 | 0 | 6.582233 | 3587637248 | 0 | `67ea4d933f433ffe4c1b9c6a8146228d306e0ec8` |
| `MultiproofConeP6Freeze.lean` | 1 | 0 | 10.869081 | 3617751040 | 0 | `aa507a0716b781fddb2d2e272a5d33bd5f39ceee` |

Every target used the private P6b object directory, shared mkdir lock, local
Lean v4.32.0, `-j1 -M4400 -DElab.async=false`, and `/usr/bin/time -l`.
The committed per-attempt `command.json`, `receipt.json`, `source.lean.txt`,
`lean.log`, `time.log` and manifest contain the exact command, full source
revision/SHA, dependency fingerprint, RSS/swap and all axiom lines. All 21
new theorems have individual `#print axioms`; the final closure adds 15
reports, including the unchanged frozen2 consumer/headline. The 36 current
reports are subsets of `{propext, Classical.choice, Quot.sound}`. In
particular:

```text
'AspisR1.MultiproofConeP6Verify.verify_in_place_owned' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.MultiproofConeP6Batch.batch_tree_owned' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.MultiproofConeP6Frozen2Stage.function_certificates' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.MultiproofConeP6Frozen2Stage.both_batches' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Failures are retained, not counted. Verify attempt 1 and Batch attempt 1
were local elaboration errors (numeral normalization and a missing namespace).
Frozen2Stage attempt 1 hit the unchanged -M4400 limit during interpreter
comparison (exit -6; 56.862117 seconds; 5,061,296,128-byte peak; zero swap).
Attempt 2 isolated `sequence_eq` as a kernel memory failure (exit 1;
19.169420 seconds; 4,655,644,672-byte peak; zero swap). The replacement makes
node recurrences opaque to incidental elaboration and proves short-circuit
congruence over an **abstract slot operation**, so the induction motive
never expands callback/node bodies. Attempt 3 checked that generic proof
at 3,562,291,200-byte peak, but had a small triple-membership elaboration
error; attempt 4 fixes it. No failed source was retried unchanged, no
resource cap was raised, and no nonstandard recovery axiom is accepted.

The [scoped audit](p6b-audit.json) checks current source snapshots, the
owned dependency closure, every standard axiom report and the retained
local Rust receipts. Reproduce with:

```sh
python3 -B tools/multiproof-cone-20261021/audit-p6b.py
```

`generate.py --check` and the pinned per-function citation check pass.
The latter inventory remains the historical **standalone extraction/solver**
ledger; its false whole-function flags are not a rejection of the new
composed certificate. The new composition status is in `p6b-audit.json`.
Six successful local Rust packets are reused: three callbacks, hash observer,
separated nodes, physical-window rebase, leaf/dedup and corrected count/guards.
Their commands, source revisions, limits, wall/RSS/swap and solver outputs
remain pinned in their original receipts. The audit checks actual relevant
function bodies where unrelated harness registration or later failing
whole-function harness text changed; it never reuses an unverified callee.
No Kani harness, SBF build, runtime suite or unchanged full manifest replay
was launched in this pass. The final import/axiom target is a focused
compatible-cache closure, **not** a coherent frozen release rebuild.

## Pass-2 endpoint and remaining work

Both requested scoped items are supplied at the named P6 boundary. This
packet adds no whole-function hypothesis beyond that local boundary.
No shipped crate, inherited Lean module, sibling candidate or wallet/key
changed. The conditional ELF rebuild gate is not triggered; no new
byte-identity measurement is claimed. All work is committed locally with
plain messages; no push or merge is performed.

Whole-source adoption still requires accepting the explicit P6
source/library/control interpretation and S2/S10's reached carrier/caller
binding. The other cones and runtime/annotation joins remain for the global
`AcceptedRunJoin`. Classification stays (c) at P6 and (d) for the unbound
actual caller. No headline premise is removed and the 100-bit release target
is not established by this packet.

## Historical pass-1 record (superseded as a composition blocker)

## Function-level P6 certificate review

Branch: `codex/cx-multiproof-p6-20261021`; base: `57ca9c452`.
No shipped source, inherited Lean module, sibling candidate, or key changed.

The checked function inventory is [p6-function-citations.json](p6-function-citations.json).
It pins each original function independently and distinguishes an extracted
owned reference from extraction of the shipped function. The original
Charon/Aeneas commands start at `reference.verify_owned`, `binary_step`,
`level_rows`, `levels`, etc. They do not extract `candidate.batch_tree` or
`multiproof.verify_in_place`. A reference extraction citation cannot be used
as a claim that those shipped functions were extracted.

## Function coverage

| Frozen function / expression | Certificate and extraction disposition |
|---|---|
| `candidate::batch_tree` | No whole-function shipped/reference certificate. Its exact body is pinned; `slotState` is an instrumented Lean composition, not its generated extraction. Source key/opening/slot/error/control adoption is still required. |
| `multiproof::verify_in_place` | Complete binary-function comparison is in `p6_certificates::verify_in_place_complete`. It compares actual copied source with extracted `reference::verify_owned`; no unverified row/level stub. Completion requires a successful solver result, not compilation or partial assertions. |
| `multiproof::binary_parent` | New `binary_parent_contract` passes on arbitrary left/right/answer and coordinate <65. Exact source body is copied with its visibility retained. Reference consumer is the extracted `reference.write_parent` / instrumented writer grammar, not a direct extraction of binary_parent. |
| `multiproof::occupied_binary_parent` | New `occupied_parent_contract` passes on arbitrary 16-digest storage, index <15, answer and coordinate <65. Exact source body, visibility change only. Same explicit reference-consumer distinction. |
| `multiproof::sibling_binary_parent` | New `sibling_parent_contract` passes for either side, arbitrary storage/index <16 and arbitrary 32-byte sibling. Exact source body, visibility change only. Same explicit reference-consumer distinction. |
| `candidate::batch_leaf` | Reuse `cone2-leaf-2`'s verified `adoption_leaf_hash_contract` and leaf-step certificate. They cover exact tags, opening offsets, component lengths, arbitrary returned digest, one call and every address byte, for all three tree kinds. They do not extract or certify the entire enclosing batch function. |
| `multiproof::node_count` | Existing corrected unread-group certificate and `CountPhysicalLevels.eighteen_count` retained. These are a local source group and kernel recurrence composition. No whole Rust node_count extraction/certificate is substituted for them. |
| Inline padding in `batch_tree` | Existing `padding_word_exact` certifies one 8-byte test; `MultiproofConePadding.padding` proves list/word equivalence. There is no separately named shipped padding function or extraction of the full `chunks_exact(...).any(...)` caller. |
| `batch_keys`, `sort_batch_keys` | Existing packed-key/insertion cuts and extracted `sort_reference.sort_rows` remain. They do not constitute a whole batch_tree certificate. |

The new callback contracts return all protocol effects: exact digest, one
call and a universally arbitrary byte of the 1/32/32 address. The Hash observer
asserts component lengths. Their only stub is `adoption_node::hash_parts`,
whose independently verified `cone3-hash-1` contract is reused unchanged.
There is no row, level, count, batch, or unverified oracle stub.

## Validation

`p6-callbacks-1`: three completed successful solver results; exit 0;
27.550004180986434 seconds; peak RSS 2,713,780 KiB; zero swaps;
source revision `e787b1e9b9dc2a189ffab5ec07202e27cfa0dbca`.
The [receipt](host-p6/p6-callbacks-1/receipt.json) records exact roots,
source hashes, dependency fingerprint, optimized environment and
MemoryHigh=6G / MemoryMax=8G / MemorySwapMax=0 / TasksMax=64.
`#print axioms`: N/A for Rust. No new Lean declaration is asserted.

The retained `MultiproofConeFrozen2Stage` attempt 2 axiom reports are:

```text
'AspisR1.MultiproofConeFrozen2Stage.accepted_batch' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.MultiproofConeFrozen2Stage.both_batches' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisR1.MultiproofConeFrozen2Stage.accepted_outer' depends on axioms: [propext]
```

That unchanged Lean target's historical receipt is reused, not replayed.
Its exact revision, wall/RSS/swap, imports and full axiom output remain in
`MultiproofConeFrozen2Stage-2/receipt.json`. This is not a new coherent
whole-release manifest replay. New tool identities are recorded as hashes
and sizes in [host-p6/toolchain.json](host-p6/toolchain.json).

## Whole-verifier attempts

The domain is all `n : usize`, arbitrary 16-entry idx/val scratch and root,
and every physical slice length ≤5504, including malformed and rejecting
inputs. Replies are independent at all 288 possible call ordinals. The gate
compares Bool, call count, any address byte at any ordinal, and independently
arbitrary idx/digest scratch coordinates, including rejection writes. It
does not compare the reference's internal n/cursor to nonexistent source
outputs. Arity is exactly Two, as in the frozen caller. The sole verified
reader stub is the unchanged `reference.read32` contract.

1. `p6-verifier-1`: exit 1, 5.180520689114928 seconds, 434,116 KiB RSS,
   zero swaps. The 288-entry generic array's initialization failed an
   unwinding assertion before a valid full-domain comparison. The apparent
   successes on equality properties are not a certificate.
2. `p6-verifier-2`: exit 1, 79.61321504204534 seconds, 4,595,776 KiB RSS,
   zero swaps. The worker stopped only its own CBMC process while the
   replacement nested-array construction was still symbolically initializing.
   Zero completed solver results. No mathematical counterexample.
   Replaced with 9,216 arbitrary primitive bytes and verified 32-byte reads;
   all 288 independent replies are retained, without an increased unwind cap.
3. `p6-verifier-3`: effective exit 65, raw Kani exit 0;
   241.90190528403036 seconds, 3,597,180 KiB RSS, zero swaps, cgroup peak
   3,705,110,528 bytes. Source revision
   `d079cbc52` (full revision in the receipt). The 240-second harness timeout
   stopped symbolic unrolling with **zero completed solver results**. The
   runner correctly rejects the raw driver's zero exit. No counterexample
   to the equality was obtained, and no equality certificate was obtained.
   Initialization is no longer the blocker: this log reaches source/reference
   control and slice/memcmp unrolling. No cap was raised or unchanged retry run.

The source snapshots, exact commands/revisions, timing, RSS, swap and cgroup
peaks for every attempt are retained under `host-p6/`. No failure is promoted
to evidence and no unchanged larger-cap rerun is allowed.

The first requested item is blocked at the complete source-function
certificate. The second depends on it and is therefore blocked too. A next
deliverable is a verified full-state callee contract/control decomposition
for the actual verifier, with its domain proved preserved by the enclosing
loop, followed by whole `batch_tree` adoption. The old failed source_row
contract must not be used as a verified stub. Reducing the input domain,
reusing one answer at all ordinals or dropping rejected scratch would not
replace this failed gate. This focused packet stops here as requested.

## Stage endpoint

`MultiproofConeFrozen2Stage.both_batches` remains unchanged. Its assumptions
remain the callback/oracle interpretation equation and six fixed-slot byte
equations, with source acceptance as the antecedent and arbitrary initial
scratch. No quantifier, conclusion or security contract is changed. The new
callback receipts alone do not identify the complete Rust batch execution
with `sourceBatch`; installing them as an axiom or a structure containing
the desired equality would not discharge the obligation.

The requested unconditional actual-source stage instantiation is therefore
not supplied by this packet. S2/S10 caller binding and the named P6 boundary
remain, together with the unfinished whole-function source adoption above.
Classification remains (c) for the instrumented stage, (d) for the actual
Rust source/caller instance. Zero headline premises removed. The release
security target is unchanged and is not established here.
