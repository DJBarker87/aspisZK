# Unified sampler focused proof evidence

Source base: `3f74f555406bfc3f0fff54f7518554d803833cc5`.

Eight final targets passed on the pinned NUC runner with Lean 4.32.0
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`). Every attempt ran in its own
4G/6G/0 high/max/swap scope, TasksMax 128, with Lean's 5000 MB threshold.
All final exit statuses and all recorded swap counts are zero.

| Target | Final attempt | Wall time | Peak RSS (KiB) | Axiom reports |
| --- | --- | --- | --- | --- |
| `R1QuerySampler` | a | 0:00.95 | 1,849,608 | 4 |
| `R1RowZeroCodec` | c | 0:00.84 | 1,805,716 | 3 |
| `R1DuplexSamplers` | b | 0:01.73 | 3,543,892 | 9 |
| `R1QuerySamplerBridge` | e | 0:00.87 | 1,841,836 | 5 |
| `R1UnifiedSampler` | c | 0:01.67 | 3,553,372 | 7 |
| `R1UnifiedContinuation` | c | 0:01.61 | 3,542,020 | 3 |
| `R1UnifiedSamplerLaw` | d | 0:01.52 | 3,548,032 | 1 |
| `R1UnifiedSamplerCheckpoint` | a | 0:01.49 | 3,521,724 | 24 |

The combined checkpoint has 24 axiom reports, and the eight successful
final targets have 56 reports in total. All use only `propext`,
`Classical.choice` and/or `Quot.sound`; none uses `sorryAx`.

All 22 attempts are retained, including 14 failed elaborations. The failed
sources and their compiler diagnostics are evidence of development attempts,
not successful proofs. The fixes concern namespace/import resolution,
missing final scan-state arguments, observer/result types, explicit sampler
projection, and choosing the correct expression to split or rewrite.
QuerySamplerBridge-c also reached its heartbeat limit during the erroneous
application; its successor corrected the term instead of raising that limit.
No memory cap was raised and no job was killed by memory pressure. Generic
query-chain proofs use symbolic induction before applying the eight-pair case.

Root reviewed all final definitions, theorem statements and proof bodies.
The artifact audit independently checked every source/receipt/sidecar hash,
resource logs, the eight archived objects, thirteen supplementary source
sidecars, and fourteen unchanged runtime-source fingerprints. RowZeroCodec
snapshots are preserved precompile local copies, independently matched to
their NUC receipt hashes. See [ROOT-VALIDATION.json](ROOT-VALIDATION.json)
and [source-manifest.json](source-manifest.json).

The archive contains only the eight final objects, with no loose `.olean`
files in this bundle. Archive SHA-256:
`1a3907f5b465f27e4768c9a2006939bcbe320b759db786757f23d4e6dde7b664`.

The pinned compiled cache was reused. This is a focused component checkpoint,
not a full historical release replay or a final private-spend security proof.
The [sampler bridge](../../UNIFIED-SAMPLER-BRIDGE.md) records the exact
scope, malformed-message totalization, and remaining protocol/source/privacy
obligations. No unchanged runtime regression was rerun.
