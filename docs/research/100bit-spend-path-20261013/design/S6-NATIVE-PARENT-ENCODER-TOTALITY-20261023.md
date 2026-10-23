# S6 original native parent encoder totality — 2026-10-23

## Enclosing claims actually closed

`AspisS6NativeSnapshotEncodeTotal.encode_total` proves, for every original native
snapshot and every mutable output slice, an actual native encoder result exists
and its returned output has exactly the original output length:

```lean
∀ snapshot output, ∃ result,
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
    snapshot output = ok result ∧ result.2.length = output.length
```

`AspisS6NativeLateEncodeTotal.encode_total` proves the same TOTAL contract for the
complete original native 1,520-byte lane-transition encoder:

```lean
∀ statement output, ∃ result,
  AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1
    statement output = ok result ∧ result.2.length = output.length
```

These are TOTAL, not ACCEPTED-ONLY. No input validity, canonicality, fixed output
length, successful validator/child encoder, model association or independently
successful checkpoint premise remains. Wrong lengths and malformed records
follow the original ordinary Rust error branches. The original Result and
returned mutable slice remain; nothing normalizes errors or replaces partial
writes with a rollback.

The same composition proves `AspisS6NativeForestTotal.validate_total` for the
complete original native forest validator on both full statement variants.
Original native transfer/withdrawal validators, their common-field writer and
both complete payment encoders are also TOTAL. All source-facing carriers are
the existing `AspisR1TerminalDecoder` native types, with every field retained.
No free `Ops` or opaque substitute is installed in these theorems.

## Concrete child installation and range reasoning

The native snapshot encoder uses its original foreach iterator body. Its exact
step theorem binds actual index_mut/copy/back operations to the actual returned
slice, on all symbolic buffers satisfying the reached bounds. Existing S2K
iterator scheduling and native digest encoder results are reused. Remaining-count
induction proves the complete native loop equals a symbolic ordered write fold;
its byte position is 160+32*level, with level0..19. Named list/slice frame facts
preserve output length without reducing a concrete 800-byte buffer.

The enclosing transition encoder now consumes that native snapshot result and
the already checked native afterstate688 encoder. Its actual checked-add and
standard Option comparison, all map_err closures, copies and returned slice
are retained. Original child failure/validation premises are discharged by the
concrete implementations, rather than grouped into a new interface assumption.
These source-level TOTAL results close the corresponding internal integer/index
range and panic/divergence obligations in the extracted semantics; they do not
establish SDK allocator/abort behavior.

## Outer forest encoder: located, not claimed closed

The legacy native decoder extraction does not contain the outer full forest
encoder declaration. An attempted helper composition exposed this through its
missing encoder closure names; it is excluded. The reference evaluator must not
be attributed to that legacy module by name.

The existing original frozen outer encoder cut is already available in
`evidence/s126-current-caller-20261021/s6-full-forest-encoder-extraction/included-encoder/`.
It preserves the full carriers and unchanged parent body, with five explicit
nested boundaries: forest validation, digest encoding, lane-transition encoding,
private-transfer encoding and withdrawal encoding. Their native implementations
now have checked totality. The next source obligation is to instantiate that
original cut through complete proved native-carrier correspondence, preserving
all errors and return/state frames. A type-schema census or opaque replacement
would not discharge that obligation. No new heavy extraction should be launched
before exhausting this existing packet. Discovery/pins are retained in
`s6-native-forest-outer-discovery-v1.json`.

Accordingly **native outer forest1880 encoder totality is not claimed here**.
Neither are the snapshot800/transition1520/forest1880 accepted byte inverses,
complete forest decoding, current SDK/account bindings or the overall S6 port.

## Source freeze

The source comparison records original native extraction revision
`0626294e34632812accf4cb14704f027368ea871`, historical freeze
`25866ec331cc7ce27dd9956609c11d32fa8fa58a`, and observed research
`564b14c4a540ec9513740c70ce82706b80a4d13c`.
Eight relevant files are byte-equal across all three. Three files differ only
by insertions: pair_forest_terminal adds semantic_public and reference/test
code; incremental_merkle and spend add cfg(kani) modules. The relevant existing
forest function spans and capacity/value-limit declarations were individually
checked byte-equal. They are explicitly **not** reported as whole-file equality.
Exact file/item hashes and the scope are in
`s6-native-parent-total-source-pins.json`; its audit tool rechecks them from git.
The prior packet supplies the original extraction and type-adapter provenance.
No production Rust, verifier, wire format or protocol parameter changed.

## Validation

All twelve selected changed targets compiled individually in dependency order,
with the atomic local lock, `-j1 -M4400`, warm caches, exit 0 and zero swap.
Thirty standard-or-empty axioms reports contain only propext, Classical.choice
and Quot.sound. Maximum selected RSS was 3322920960 bytes; summed selected
wall time was 198.086 seconds. No SBF build, heavy NUC job or unchanged full
manifest replay ran.

| Target | Wall seconds | Peak RSS bytes | Swap |
|---|---:|---:|---:|
| `S6NativeSnapshotValidatorTotalV1` | 22.100 | 3285303296 | 0 |
| `S6NativeSnapshotStoreV1` | 24.198 | 3227893760 | 0 |
| `S6NativeSnapshotLoopStepV1` | 7.885 | 3322920960 | 0 |
| `S6NativeSnapshotLoopV1` | 15.797 | 3203416064 | 0 |
| `S6NativeSliceFrameLengthV1` | 15.055 | 2228781056 | 0 |
| `S6NativeSnapshotEncodeTotalV1` | 16.547 | 3321544704 | 0 |
| `S6NativeLateEncodeTotalV1` | 26.277 | 3158999040 | 0 |
| `S6NativePaymentValidatorTotalV1` | 18.409 | 3257139200 | 0 |
| `S6NativePaymentCommonEncodeTotalV1` | 15.180 | 3305816064 | 0 |
| `S6NativePaymentEncodeTotalV1` | 12.422 | 3280273408 | 0 |
| `S6NativeForestHelpersV1` | 13.147 | 3292151808 | 0 |
| `S6NativeForestValidatorTotalV1` | 11.070 | 3306635264 | 0 |

The first snapshot parent proof hit the default elaboration heartbeat limit
while matching an expanded mutable buffer. It was not rerun with larger
options. The replacement keeps the buffer symbolic, uses named slice-frame
length facts, and matches the actual zero-start iterator constructor explicitly.
The accepted enclosing snapshot target is v5. Earlier failed attempts and
missing-declaration diagnostics remain excluded source-only evidence; no failed
sorryAx/custom-constant report is accepted. No resource ceiling was raised.

Exact source/revision/tool/direct-import pins, commands, status, wall/RSS/swap
and audits are retained in the selected receipts. The source-only target map is
`s6-native-parent-total-targets.json`; its transitive object hashes are in
`s6-native-parent-total-import-pins.json`. No binaries are distributed.
Audit commands:

```
python3 tools/s6-full-forest-roundtrip-20261023/check-native-parent-total.py
python3 tools/s6-full-forest-roundtrip-20261023/check-native-parent-source-pins.py
```

## Remaining

Complete the native snapshot decoder and byte inverse, consume it in the
transition and full forest byte laws, and install the existing original outer
forest encoder cut through proved carrier/callee correspondence. Then connect
the complete serializer and decoded-public reuse to actual first/first_decoded
and current adapter stage1 with release observer None, ordered reads, errors,
state/ownership, allocation and abort-prefix effects. S1's preparation/gamma and
resumed-powers caller ports remain. S2 stays with its external owner. The
≤2^-100 per-attempt target is not yet established.
