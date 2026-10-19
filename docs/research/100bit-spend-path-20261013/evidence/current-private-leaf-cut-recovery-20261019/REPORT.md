# Actual private leaf and candidate path: commitment-cut recovery

Three focused proof targets now connect the unchanged private-leaf helper and the emitted explicit-child candidate Merkle checker to the existing commitment-cut recovery theorem.

- `RawPrivateLeafCall.leaf_equation` proves the entire source helper equals its own digest call on the exact three parts, preserving success, errors and divergence. `leaf_literal_bytes` proves those parts flatten to exactly `0x10 || tag || value || salt32`; salt length follows from the actual source array type.
- `RawPrivateLeafAcceptedPath.accepted_private_leaf_path` derives a six-level authentication path and the full seven-call ordered leaf/parent input-answer trace from successful actual leaf hashing and the candidate checker returning true. Under inclusion of these exact calls in one consistent global log, the ideal path reaches the advertised root.
- `RawPrivateLeafCutRecovery.accepted_private_leaf_recovered_before_frame` uses that source execution result to discharge the separately assumed ideal acceptance and ideal opening-read premises of the retained cut-recovery theorem. Under the single existing collision exclusion and commitment-frame target gates, the actual opened bytes and salt are recovered from queries made strictly before the first frame read. There is no additional per-coordinate collision charge.

**Open premises and scope.** Inclusion in the complete chronological caller log is still explicit. The frame read/target, global log consistency, query bound and collision exclusion are explicit. This packet does not derive the full caller's frame/root relationship, query geometry, strict field decoding, a distributional law, or complete 100-bit soundness. The original production path checker still uses `from_fn`; the path side here is the unadopted explicit-child candidate. The private-leaf helper itself is unchanged source. No production code or CU/artifact result changed.

The exact helper was extracted from source revision `20e596416f8e0fe6f2b253e19b084a2a8faaa2bc`; the cut consumer uses `76dc413d9 + RawPrivateLeafCutRecovery-v3`. Source file/spans, exact zero-dependency harness, Charon/Aeneas commands/tool hashes and LLBC are retained. Charon exited 0 in 0.201 s (107,360 KiB process RSS); Aeneas exited 0 in 0.402 s (61,424 KiB); both had zero cgroup swap. LLBC SHA `7ff7b6b3162d5e2690b91fb0e0fdb99075ddd4b34ae2d602b0d0f99215de8f8b`. No external-function template was emitted.

| Focused Lean target | Exit | Wall | Process RSS KiB | Cgroup peak bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| Private leaf Types | 0 | 2.006 s | 2,619,612 | 298,049,536 | 0 |
| Private leaf Funs | 0 | 1.806 s | 2,620,456 | 286,334,976 | 0 |
| RawPrivateLeafCall | 0 | 2.006 s | 2,626,448 | 306,020,352 | 0 |
| RawPrivateLeafAcceptedPath | 0 | 1.906 s | 2,621,816 | 292,712,448 | 0 |
| RawPrivateLeafCutRecovery | 0 | 2.008 s | 2,633,308 | 288,665,600 | 0 |

All Lean runs used the pinned native Lean 4.32.0 compiler, one thread, interpreter threshold 3200 MB, 120-second watchdog and swap-free scoped limits. Leaf owners/call used 1 GiB high/2 GiB max; the two dependent consumers used 512 MiB high/1 GiB max, based on their focused predecessor's measured physical usage. Full source/object/import pins, exact commands, preflights, GNU-time logs, receipts and printed axioms are retained in the frozen kits.

The leaf-call four axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. The path and cut consumers additionally use the existing Aeneas `core.fmt.Formatter` type boundary through the candidate path's slice-array unwrap; they are not standard-only results. There is no `sorryAx`.

Six unchanged already-checked cut/collision objects were copied from the pinned local Lean 4.32 cache with source/object hashes instead of rebuilding their transitive closure. The new native consumer compiled against them and printed its axiom set. The missing native search-path diagnostic and a subsequent unused namespace-open error are retained; neither is a proof failure hidden as a successful run. Two resource admissions were held before any leaf-call compiler process started while another scoped job held a reservation; those records are retained. No full package or manifest replay was run.
