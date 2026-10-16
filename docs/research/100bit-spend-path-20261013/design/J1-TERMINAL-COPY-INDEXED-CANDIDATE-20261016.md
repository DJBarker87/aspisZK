# Isolated terminal array-construction and fold candidate

An isolated source candidate now passes optimized Rust compilation, Charon,
and Aeneas. It replaces 18 opaque `core::array::from_fn` calls with a local
safe initializer loop and replaces the terminal's two owning-array reverse
folds with indexed reverse loops. The change makes these operations available
as generated recursive definitions for focused source proofs.

The helper accepts a `Copy` initializer, initializes the fixed array, invokes
the callback once at each increasing index, and overwrites that cell. The
call sites use existing zero values as initializers and retain their callback
bodies. The reverse loops retain semantic-entry order 23 down to 0 followed
by Poseidon-entry order 3 down to 0. Production adoption, old/new semantic
equivalence, full terminal verification and fresh runtime/CU gates are not
established by this extraction experiment.

## Retained evidence

The [root review](../evidence/terminal-copy-indexed-candidate-20261016/root-review.json)
independently checks the 133-row source snapshot, three changed files including
the merged extraction crate root, stage receipts, resource reservations and
raw timing logs. Seventeen embedded local source files in the LLBC match the
input bytes exactly. The original/adapted LLBC differ only at the unique M31
constructor's metadata rename; reversing that change reconstructs the
original JSON exactly.

The archive preserves the original runner and receipts. It includes an exact
`actual-merged-input.patch` and the three changed F base files. The earlier
`candidate.patch` used source-kit crate-root framing and is retained as a
draft, not described as the exact merged-input patch.

| NUC stage | Exit | Wall time | Peak process RSS (KiB) | Swap |
|---|---:|---:|---:|---:|
| Rust release build | 0 | 65.413 s | 810,392 | 0 |
| Charon | 0 | 73.453 s | 1,115,932 | 0 |
| Aeneas | 0 | 9.287 s | 332,288 | 0 |

Each stage used its own 4 GiB high / 6 GiB max / swap-zero scope and a
300-second timeout. Rust used release opt-level 3 with overflow checks,
offline locked dependencies, and one job. The pinned warm cache was reused;
it is excluded from the evidence archive.

## What the output establishes

The wrapper, public terminal method, `terminal_parts` and `composition_parts`
are local transparent structured definitions. The LLBC has 336 non-null
function records: 242 local transparent structured functions and 94 other
records. A body field alone is not evidence that a function is transparent.
The separate translation metadata reports 220 functions, 59 types and 60
trait implementations; these are different inventories.

Relative to G, all 58 type docblock bodies and 204 shared function docblock
bodies are byte-identical. Thirty-four shared function docblocks changed and
two helper docblocks were added. These counts include grouped trait
dictionary declarations and are not counts of Rust functions.

External function templates fall from 20 to 17. Only `array.from_fn` and the
owning iterator's `next` and `next_back` disappear. The
[remaining-template map](../evidence/terminal-copy-indexed-candidate-20261016/external-template-map.md)
records array-map/fold, bit-intrinsic, option/result and mutable-iteration
dependencies and the limits of historical proof reuse. Absence from a direct
call graph does not prove absence through trait dispatch.

Focused proofs of the new helper, real callers and indexed loops are separate
deliverables. The complete source/model relation and end-to-end security
theorem remain open. No new performance or 100-bit soundness claim follows
from this translation result.
