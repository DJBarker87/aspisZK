# R633 actual packed-block result

The complete selected 31-byte block execution now produces exactly eight
masked U32 writes, in source order, and the exact accumulated invalid mask.
`R633PackedBlockResult.block_result` has only the destination bound
`8 * (block.val + 1) ≤ N.val`; read, cast, index, update, iterator success,
and input canonicality are derived rather than assumed. The incoming output
array and invalid mask are arbitrary. `block_mask_accepted` proves the outgoing
mask accepts iff the incoming mask accepts and all eight masked words are
strictly below P=2147483647. Value P is retained and rejected.

R624 supplies the complete generated eight-iteration loop result.
R631 proves the actual standard-library chunk primitive returns full chunks
of exactly 31 bytes, count `bytes.length / 31`, and remainder length
`bytes.length % 31`. These results do not yet prove whole accepted output
canonicality, radix-2^31 serialization, quotient extraction, privacy, or
soundness. The first remaining proposition composes the blocks across the
actual 104/48 destinations, then identifies their serialized values.

## Verification

All targets used pinned Lean 4.32, `lake env lean -j1 -M4500`, and separate
systemd scopes with MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128.
Source revision: 2201f823ad3df8130400ba78eef59045392675fe.

| Target | Successful run | Exit | Wall | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| R624DecoderInnerExecution.lean | 1791107622918336000 | 0 | 2.53s | 3788476 | 0 |
| R631DecoderChunkShape.lean | 1791107883559263000 | 0 | 1.71s | 3754392 | 0 |
| R633PackedBlockResult.lean | 1791107844177857000 | 0 | 1.39s | 3743220 | 0 |

All 25 requested axiom reports are saved completely in receipts and logs.
They contain only propext, Classical.choice, Quot.sound, with the inherited
opaque `core.fmt.Formatter : Type` additionally present in R633.block_result.
That is a type constant used by the retained unwrap/Debug path, not a behavior
proposition. No successful report contains sorryAx. Failed development
attempts are retained as failures. GNU time measures Lean-child peak RSS;
wrapper cgroup MemoryPeak is not aggregate Lean RSS.

The evidence manifest records exact target checksums, dependency source
copies, the cached R624 import pin, the library source, frozen verifier
revision 6677d5f1310ff7373301fbd79f186278f772e68a and immutable extraction
input. Sources were promoted byte-for-byte from green snapshots. Successful
unchanged checks were not repeated. No verifier/security parameter changed;
no CU benchmark or unchanged regression ran. Saved CU remains 999790/999532.

Evidence: [r633-packed-block-result](evidence/r633-packed-block-result/).
