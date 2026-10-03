# R482/R483 packed shared-read model proofs

R482 and R483 compile in the pinned Lean 4.32 cached workspace. They provide a storage-refinement lemma and a small checked shared-reference/read-place fragment for the selected packed QM31 representation. Their successful source snapshots exactly match the promoted Lean files, byte for byte. Source revision at compilation: `95d940b0d08adaee737a2394d3d49a258f39e18a` (`research/v8-r64-guarded-m31-20260929`). SHA-256 values: R482 `94e7effc9a6c6861c86440fc731458b7ea8c804b85a9e7ed8413bde51c5fa614`; R483 `78938bc0968dcdcbaa130c09e026e593dc8a29115bd5fece0c0281865d10f78f`.

## What is proved

R482 maps allocations and heaps through a representation function while preserving their address and bounds fields. It proves that reads commute with this mapping, including absent origins, missing allocations, and invalid pointer/alignment cases. Encoding a QM31 heap into packed 128-bit cells and decoding it again is identity, so reads from that explicitly modeled heap round-trip for every pointer.

R483 defines a proposed state fragment containing packed heap cells, allocation-liveness and read-permission flags, and locals. It defines checked reads, shared-reference acquisition, copying through an acquired reference, and the two selected dereference forms. The proved frame results preserve heap, liveness, and readability for supported and unsupported fragment outcomes. A backed-pointer read theorem returns the packed cell under explicit heap lookup, liveness, readability, and bounds hypotheses. `unsupported` means this fragment does not justify execution; it makes no claim about the source program's Rust error behavior.

These are explicit heap-refinement and proposed checked-reference-fragment results. They do **not** prove that the actual Rust caller establishes the represented heap, liveness, permissions, aliasing, lifetime, or frame conditions; they do not establish native execution of either selected read, the Aeneas memory semantics, or the complete freeze fold. No privacy or end-to-end security claim follows from these files.

## Focused compilation records

Both runs used `lake env lean -j1 -M4500` in the pinned cached workspace under `systemd-run --user --wait --collect --pipe`, with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Peak RSS is GNU time's Lean-child RSS in KiB; swap is zero in each case.

| Target | Run ID | Exit | Wall time | Peak RSS | Source SHA-256 |
|---|---:|---:|---:|---:|---|
| `AspisV8R19/R482PackedAllocationRead.lean` | `1791038007033804000` | 0 | 2.15 s | 3,718,384 KiB | `94e7effc9a6c6861c86440fc731458b7ea8c804b85a9e7ed8413bde51c5fa614` |
| `AspisV8R19/R483SharedReadPlace.lean` | `1791038150055147000` | 0 | 1.91 s | 3,732,164 KiB | `78938bc0968dcdcbaa130c09e026e593dc8a29115bd5fece0c0281865d10f78f` |

## Complete axiom output

R482:

```text
'AspisV8R19.R482PackedAllocationRead.mapAllocation' depends on axioms: [propext]
'AspisV8R19.R482PackedAllocationRead.mapHeap' depends on axioms: [propext]
'AspisV8R19.R482PackedAllocationRead.read_map' depends on axioms: [propext, Quot.sound]
'AspisV8R19.R482PackedAllocationRead.mapHeap_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R482PackedAllocationRead.read_packed_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound]
```

R483:

```text
'AspisV8R19.R483SharedReadPlace.readPacked' depends on axioms: [propext]
'AspisV8R19.R483SharedReadPlace.acquireShared' depends on axioms: [propext]
'AspisV8R19.R483SharedReadPlace.copyShared' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R483SharedReadPlace.refSharedDeref' depends on axioms: [propext]
'AspisV8R19.R483SharedReadPlace.copySharedDeref' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R483SharedReadPlace.put_frame' depends on axioms: [propext]
'AspisV8R19.R483SharedReadPlace.refSharedDeref_frame' depends on axioms: [propext]
'AspisV8R19.R483SharedReadPlace.copySharedDeref_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R483SharedReadPlace.copy_acquired' depends on axioms: [propext, Classical.choice, Quot.sound]
'AspisV8R19.R483SharedReadPlace.readPacked_backed' depends on axioms: [propext, Quot.sound]
```

## Preserved run evidence

`evidence/r482-r483-packed-shared-reads/` contains exact source snapshots, receipts, and complete logs for both successful runs and both preceding failed attempts. The failed R482 run (ID `1791037920846397000`) records the ambiguous `read` and proof simplification failures, including `sorryAx` in its failed axiom report. The failed R483 run (ID `1791038106070315000`) records the frame, acquired-copy, and backed-read proof failures, also including `sorryAx`. Both successful receipts report no `sorryAx`. `SHA256SUMS.txt` records checksums for the promoted targets and all preserved run files.

## First remaining proof

The next missing native-source proposition is a semantics bridge from each pinned selected dereference operand and the actual caller's allocation, liveness, shared-read permission, and alias/lifetime context to this checked fragment's supported execution and frame. Until that is derived from the actual Rust/Aeneas execution, R483 remains a proposed fragment rather than a proof of native memory behavior.
