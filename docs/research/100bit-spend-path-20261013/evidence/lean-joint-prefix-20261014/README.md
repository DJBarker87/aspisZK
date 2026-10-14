# Joint-prefix focused proof evidence

Source base: `f9183a8c38df9e2ab63a5b2688006e6c6ba2b898`.

Eleven final targets passed on the pinned NUC runner using Lean 4.32.0
(`8c9756b28d64dab099da31a4c09229a9e6a2ef35`). Each attempt used a separate
4G/6G/0 high/max/swap scope, TasksMax 128, and Lean's 5000 MB threshold.
Every final exit status is zero; all recorded swap counts are zero.

| Target | Final attempt | Wall time | Peak RSS (KiB) | Axiom reports |
| --- | --- | --- | --- | --- |
| `R1TableBeforeOrder` | c | 0:00.78 | 1,804,648 | 2 |
| `R1JointPrefixAnswers` | a | 0:01.52 | 3,536,388 | 5 |
| `R1PrefixPendingFacts` | b | 0:01.53 | 3,538,104 | 2 |
| `R1JointNextLaw` | b | 0:01.60 | 3,540,692 | 4 |
| `R1OpeningPrefixAnchor` | a | 0:00.96 | 1,813,584 | 1 |
| `R1PrefixRecordFacts` | a | 0:01.54 | 3,541,800 | 4 |
| `R1JointNextTrace` | a | 0:01.61 | 3,545,096 | 1 |
| `R1OpeningAnchorCells` | a | 0:00.87 | 1,812,292 | 1 |
| `R1JointNextBound` | a | 0:01.45 | 3,534,832 | 1 |
| `R1OpeningQueryTrace` | b | 0:01.61 | 3,545,220 | 1 |
| `R1JointPrefixCheckpoint` | a | 0:01.47 | 3,532,168 | 22 |

The combined checkpoint imports the preceding opening-prefix checkpoint
and the new composition modules. Its 22 reports, and all 44 reports across
successful targets, contain only `propext`, `Classical.choice`, and/or
`Quot.sound`. The 16 attempt records include five failures and eleven final
successes. Failed compiler outputs may contain `sorryAx` from elaboration
errors; none is a successful proof result. Exact failed source snapshots
are retained alongside the logs and receipts.

The failed attempts record two table-order type mismatches, pending-fact
type mismatches, a background-law rewrite mismatch, and a missing namespace
for `bfollow` in the combined theorem. Each was followed by a changed source
and focused compile. No memory-pressure failure or cap increase occurred.

Root reviewed all final theorem statements and proof bodies, then checked
all source/receipt/sidecar hashes, resource log agreement, final object
archive members, four supplementary source-hash sidecars, and all fourteen
central runtime source fingerprints. Current Lean sources match the final
snapshots; the runtime fingerprints remain unchanged. See
[ROOT-VALIDATION.json](ROOT-VALIDATION.json) and
[source-manifest.json](source-manifest.json).

The object archive contains only the eleven final `.olean` objects; no loose
objects are shipped. Archive SHA-256:
`cf094cef48839ef3d7dda3ab1b40717a0464f0612e7eb1f8cdc8a60c4857709f`.

This is a focused component checkpoint using the pinned compiled cache.
It is not a from-scratch historical manifest replay, a source refinement,
or the final private-spend theorem. See the root-owned
[joint-prefix bridge](../../JOINT-PREFIX-BRIDGE.md) for exact premises and
remaining obligations. No unchanged runtime regression was rerun.
