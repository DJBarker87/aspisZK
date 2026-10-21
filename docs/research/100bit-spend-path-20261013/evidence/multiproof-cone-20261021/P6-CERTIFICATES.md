# Function-level P6 certificate review

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
