# NMB cut table (in progress)

Target not yet established. No full native row credit or promotion.

| Cut | Frozen source | Contract / assertion | Control | Verdict |
|---|---|---|---|---|
| 344-owned-error-boundary | r1_pool_adapter_owned.rs:447–460 | ACTUAL stage1 contract, modifies empty, all original descriptors retained; arbitrary selected byte of key/owner/flags/length/byte-availability/program/instruction at the owned-child call returned unchanged through ProgramError::Custom | SAME harness under NMB_invert, pending positive verdict | K001 TIMEOUT124 / no credit |

K001 is a changed full-payload/aliasing shape, not NLQ's narrow checkpoint-window oracle. All three physical buffers and admitted snapshot payloads use Kani exact_vec with independent arbitrary bytes at58295/1880/1768. Snapshot's entire owned payload is unconstrained, never zero-filled. Plain snapshot and stage1_owned stubs are cut-point overapproximations, not stub_verified contracts on Ref or ProgramResult. The callback transports one arbitrary selected descriptor coordinate through its return value, with no writable static, Option<fn>, or global observer. Full snapshot byte equality is supplied by CLOSED343 at composition; K001 alone does not assert it. The malformed-length complement and every other segment remain open.

The strict source validator removes exactly two cfg(kani) stage1 annotations plus the recorded cfg-only harness-module suffixes, then hashes EVERY frozen source byte. Shared gate/launcher infrastructure is unchanged. Full resolved offline graph and pre/post frozen lock hashes are checked for every native scope. Exact canonical KMX files and patch bytes are validated. No field multiplication or SHA is unwound.

K002 is a RESOURCE DIAGNOSTIC, not a full parent segment certificate: source array assembly with one arbitrary58295-byte Vec, observed at one arbitrary offset. CBMC timed out90s (scope94.292281257s,3319820KiB,swap0); frozen offline graph and unchanged lock pass. No matched control or row credit. The full-vector construction shape is retired; next native work must split the source operation into a true window or another independent stretch.
