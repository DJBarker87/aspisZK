# Joint-decoder focused proof evidence

Source base: `005b87b2bcf20daacf7acdc626386fc9cca9423e`.

Eleven final targets passed on the pinned NUC runner with Lean 4.32.0
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`). Each attempt used its own
4G/6G/0 high/max/swap scope, TasksMax 128, and Lean's 5000 MB threshold.
All final exit statuses and all recorded swap counts are zero.

| Target | Final attempt | Wall time | Peak RSS (KiB) | Axiom reports |
| --- | --- | --- | --- | --- |
| `R1IndexedMessage` | b | 0:00.81 | 1,815,364 | 4 |
| `R1PrefixRecordLength` | b | 0:01.49 | 3,534,988 | 3 |
| `R1BackgroundLawMap` | b | 0:00.73 | 1,797,476 | 1 |
| `R1JointContext` | b | 0:01.56 | 3,550,196 | 2 |
| `R1JointContextSound` | b | 0:02.05 | 3,547,248 | 2 |
| `R1JointDecoder` | a | 0:01.56 | 3,546,036 | 3 |
| `R1JointDecoderTrace` | a | 0:01.63 | 3,547,888 | 1 |
| `R1JointDecoderBound` | b | 0:01.56 | 3,542,748 | 2 |
| `R1JointRhoBound` | a | 0:01.63 | 3,555,328 | 2 |
| `R1TranscriptView` | b | 0:01.60 | 3,552,128 | 5 |
| `R1JointDecoderCheckpoint` | a | 0:01.52 | 3,533,204 | 25 |

The combined checkpoint imports the preceding joint-prefix checkpoint and
the new decoder, bound and transcript-view modules. All 25 checkpoint reports
and all 50 reports across successful targets contain only `propext`,
`Classical.choice`, and/or `Quot.sound`, or no axioms. `ordinary_cons` is
axiom-free and appears once in its module and once in the combined checkpoint.

All 18 attempts are retained: seven failures and eleven final successes.
Failed elaborations may report `sorryAx`; none is treated as a successful
proof. Each failed source was changed before the next focused compile.
The decoder-bound attempt a passed a rational indicator where `chainB`
requires the bad predicate and also lacked explicit `Option.some` injection.
Correcting those two terms removed the type and recursion-depth errors;
no recursion or memory cap was raised. Other failures were namespace,
constructor/type, option-simplification or no-goals-left errors. No job was
killed by memory pressure.

Root reviewed all final statements and proofs. The artifact audit checked
current source and final snapshot equality, every attempt's source/receipt/
sidecar hash, resource logs, eleven archived objects, three supplementary
source-hash sidecars, and fourteen unchanged central runtime fingerprints.
See [ROOT-VALIDATION.json](ROOT-VALIDATION.json) and
[source-manifest.json](source-manifest.json).

The object archive contains only the eleven final `.olean` files, with no
loose objects in this bundle. Archive SHA-256:
`fca4064b525c533e286eaf38c79769db22830cf68b236a60ea614a023a431bcb`.

The pinned cache was reused. This is a focused component checkpoint, not a
from-scratch historical manifest replay or the final private-spend theorem.
The [decoder bridge](../../JOINT-DECODER-BRIDGE.md) records the exact scope
and remaining protocol, source and privacy obligations. No unchanged runtime
regression was rerun.
