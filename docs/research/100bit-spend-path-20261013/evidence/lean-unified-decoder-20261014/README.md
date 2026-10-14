# Unified decoder focused proof evidence

Source base: `121c6101d2e2aa571b9106afe403cbcfd60c3ec8`.

Thirteen final targets passed using the pinned NUC Lean 4.32.0 toolchain
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`) and compiled cache. Every
attempt ran in a separate 4G/6G/0 high/max/swap scope, TasksMax 128, with
Lean's 5000 MB threshold. All final exit statuses and recorded swap counts
are zero.

| Target | Final attempt | Wall time | Peak RSS (KiB) | Axiom reports |
| --- | --- | --- | --- | --- |
| `R1UnifiedRun` | b | 0:01.69 | 3,542,960 | 5 |
| `R1CompletedView` | c | 0:01.70 | 3,536,028 | 3 |
| `R1JointRecoveryTotal` | b | 0:01.58 | 3,538,580 | 3 |
| `R1UnifiedPayloadValue` | a | 0:01.43 | 3,541,796 | 1 |
| `R1UnifiedRecords` | b | 0:01.55 | 3,547,968 | 3 |
| `R1UnifiedRecordCompletion` | e | 0:01.56 | 3,545,156 | 1 |
| `R1JointTranscriptView` | b | 0:01.55 | 3,548,792 | 3 |
| `R1JointUnifiedLaw` | b | 0:01.60 | 3,544,132 | 1 |
| `R1UnifiedQueryRun` | b | 0:01.57 | 3,546,336 | 5 |
| `R1JointActualView` | d | 0:01.50 | 3,542,412 | 1 |
| `R1JointUnifiedDecoder` | b | 0:01.49 | 3,547,204 | 3 |
| `R1JointUnifiedBound` | a | 0:01.53 | 3,544,960 | 1 |
| `R1UnifiedDecoderCheckpoint` | a | 0:01.41 | 3,525,256 | 30 |

The checkpoint reports 30 axiom audits. The final targets, including that
checkpoint, report 60; one superseded successful target adds one further
historical report. All use only `propext`, `Classical.choice` and/or
`Quot.sound`, or no axioms. `JointTranscriptView.view_some` is axiom-free
and appears both in its module and the checkpoint. No successful result
uses `sorryAx`.

All 29 attempts are retained: 15 failed, one superseded success and 13 final
successes. Failed elaborations may contain `sorryAx`; they are not release
proofs. `UnifiedRecords-a` reached the heartbeat limit while normalizing a
concrete row-26 transcript (10.41 s, 3,524,116 KiB, zero swap). The replacement
first proves the payload value for a symbolic prefix, then applies it to
the run. `UnifiedRecords-b` passed in 1.55 s without changing the heartbeat
or memory limit. The remaining failures were namespace resolution, binder,
rewrite-direction, reserved-keyword, or already-closed-goal errors. No job
was killed by memory pressure. `JointActualView-d` only clarifies the scope
comment after successful attempt c; its theorem and proof are unchanged.

Root reviewed the final theorem statements, premises and proofs. The
independent artifact audit checked all source/receipt/sidecar hashes, every
resource receipt against its time log, the thirteen archived objects,
seventeen supplemental source-hash sidecars, and fourteen unchanged runtime
fingerprints. Some worker snapshots were preserved locally before compilation
and matched against their NUC receipt hashes; the manifest records provenance.
See [ROOT-VALIDATION.json](ROOT-VALIDATION.json) and
[source-manifest.json](source-manifest.json).

The archive contains only the thirteen final objects; there are no loose
`.olean` files in this bundle. Archive SHA-256:
`575aa9af3b25a67c2749bb8ce2fb9474fc8d18d97453d525a1c3afc92697c43b`.

This is a focused transcript/decoder component checkpoint. It is not a full
historical replay, complete first-read injection proof, Rust refinement, or
final soundness/privacy theorem. The [bridge document](../../UNIFIED-DECODER-BRIDGE.md)
records the exact scope and remaining obligations. No unchanged runtime
suite was rerun.
