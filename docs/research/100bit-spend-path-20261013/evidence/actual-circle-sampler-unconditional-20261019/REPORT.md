# Actual circle sampler: unconditional totality and circle validity

Every 32-byte input block and either circle row now make the retained actual emitted `sampler.circle_sample` wrapper return a point on the R0P circle. The checked endpoint `RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle` has no assumed sampler success, mapper success or canonical-parameter premise. This advances sampler rows 25–26 independently of the commitment format.

The new canonicality bridge copies the actual public byte sampler's already-proved total canonical output into the wrapper/R72 representation. The endpoint then reuses the retained actual secure-mapper execution and both actual fallback paths. No polynomial field or circle algebra has been reproved. Production Rust is unchanged.

This establishes totality and the circle equation. It does not establish the output distribution, the complete literal row-sampler correspondence or whole-verifier soundness. The exceptional fallback probability must remain explicit in the distribution proof. The selected R72 source/import-owner provenance is being retained separately; this packet records the exact direct import hashes used, rather than declaring an unverified source correspondence.

| Checked target | Exit | Wall | Peak process RSS KiB | Cgroup peak bytes | Swap bytes |
| --- | --- | --- | --- | --- | --- |
| Actual sample canonicality V1 | 0 | 2.207 s | 3,841,440 | 395,534,336 | 0 |
| Unconditional actual policy V1 | 0 | 1.906 s | 4,082,396 | 417,906,688 | 0 |

All four printed theorem axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`. The target receipts contain free-form source-revision labels, not exact Git revisions; the target source/object and direct-import hashes are exact. This publication was assembled on research after `7f8c0f317` without changing those sources. Commands, compiler hash, ordered import roots, scope reservations, GNU-time output, receipts and failed v6–v8 predecessor snapshots are retained in the immutable archive.

Archive SHA256: `9a903f37b593afbe175c90ed91e5abee1400a7185e5434889ce44cac8d4084f6`.
Manifest SHA256: `60ca1102c6ea459709fff7d99f9a9ed103e7fba2f344c9f673883349d929cb5c`.
Publication validated both target source/object hashes, zero-swap successful receipts and exact axiom logs; `payload-sha256.json` inventories all 40 retained payload files. Readable sources are under `lean-candidates/current-circle-wrapper-20261019`. No full manifest replay was run.
