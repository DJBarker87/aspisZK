# R597 sampled chord core

R597 composes the selected secure-circle sampler with the actual chord construction and the 271-column core determinant scaling result. For two successful calls to the selected R156 `challenge_secure_circle_point`, under the same arbitrary total hash function and states, and distinct returned points, it derives successful canonical coordinates, parameters with nonzero imaginary parts, distinct parameters, the actual `rawData` result, its three chord coordinates, and the determinant scaling/nonzero equivalence from R595.

The theorem is `AspisV8R19.R597SampledChordCore.sampled_chord_core` in [R597SampledChordCore.lean](lean/AspisV8R19/R597SampledChordCore.lean). The source file was promoted byte-for-byte from the root-reviewed green snapshot: SHA256 `cc7bc40f59095afd584e6ae6ec0754c411541b2abe33faae9bc471484c054ab8`; source revision `35c57c8989c08664ebc43919409556a4686c530a`.

The successful focused Lean check was run against the pinned cached workspace with `-j1 -M4500`, in a systemd user scope capped at `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. It exited 0 in 1.71 seconds, with peak Lean-child RSS 3,764,448 KiB and swap 0. Its complete axiom output is:

```text
'AspisV8R19.R597SampledChordCore.sampled_chord_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 core.fmt.Formatter]
```

`core.fmt.Formatter` is the inherited opaque Aeneas type constant declared in the bundled pinned source copy `source/Fmt.lean` (`axiom core.fmt.Formatter : Type`), not an assumed proposition. The selected sampler’s checked slice conversion passes a `Debug` witness through `Result.unwrap`, which accounts for that type dependency.

The evidence directory contains all three attempts, their exact source snapshots, logs, and receipts. The first two failed checks reported `sorryAx`; the final source fixed the proof construction and compiled with no `sorryAx`. No unchanged check was replayed for promotion.

The result binds successful selected circle-sampler executions to the chord-core algebra. It does not yet bind the complete callback chronology, the gamma-weighted mutable-power freeze fold, or the actual challenge distribution. Universal G compatibility, privacy simulation, soundness extraction, and probability-loss accounting remain open. The first required next bridge is the complete source chronology through the callback together with its shared-oracle law.

Evidence and checksums are recorded in [evidence/r597-sampled-chord-core](evidence/r597-sampled-chord-core/).
