# R1 selected-mask full-coefficient batch: source review

Reviewed read-only against the pinned extraction/Lean workspace
`/home/dombarker/project-offloads/aspis-r1-mask-lean432-20261015`, its attempt
snapshots and receipts, and the extracted `Funs.lean` source. This is a
mathematical-source and build-provenance audit, not a Rust-to-Lean refinement
claim.

## Finding

The 15 selected final targets all have successful Lean 4.32 receipts whose
source hashes match their successful attempt snapshots and whose output
objects match the recorded object hashes. The selected declarations emit 51
axiom reports; the reported axioms are subsets of
`{propext, Classical.choice, Quot.sound}`. No selected final report contains
`sorryAx`. Maximum recorded RSS is 3,144,004 KiB, cumulative selected-target
wall time is 24.836 seconds, and every selected attempt records zero swap.
The run receipts record the 4 GiB high / 6 GiB max / zero swap / 128 task cap.

There is one direct-import source-pin discrepancy in the recorded chain:
`populated-meaning-i` records `ExtractedMaskCallerModel` source SHA
`876ed33b687f67d37772e44d507d58a09f2edfed9e4759e33a5bb59cd70af021`, while
the object it imported is SHA
`5c9fdf5d1634d3731c3b6344b2947990c0fee51ec677f33374b881f79678c631`. That
object is exactly the output of successful `caller-model-h`, whose source and
snapshot SHA is
`4e675d196e7d3c281674d440aa8d92c554cc9d29249cb2ad0e85d27121d12e1c`.
At audit time the shared `sources/ExtractedMaskCallerModel.lean` path had
been restored to the latter SHA, while the old `populated-meaning-i`
receipt remains immutable and still records the former source pin. Thus the
green object dependency is identifiable through the successful `h` receipt,
but the `i` receipt's captured import-source field is not a matching
source/object pair. Preserve both historical hashes and label this
reconciliation explicitly in the evidence manifest; do not rewrite the old
receipt as if it had recorded `4e675d...`.

Apart from that CallerModel source-field mismatch, direct imported object
hashes checked for these receipts match the recorded hashes. The corresponding
source hashes match where a source file is part of the imported-source pin;
external Aeneas/Mathlib imports are represented by their object hashes.

## What the checked declarations establish

The selected generated Aeneas file is
`AspisR1SelectedMaskProbe/Funs.lean`, SHA
`4aa955ab74e6db926d02bdbee7dd9cdf5f755b019311dd3c67599bd8d97aa395`.
Its extracted source annotations identify `src/state_only_hiding.rs`, with
the selected-mask caller and three loops at the referenced lines. In the
generated definitions, loop 0 ranges over the 16-element C1 array, reads a
column, computes `column &&& 3`, applies `mul_tower_basis`, reads the factor
exponent table, and updates the 27-element coefficient array. Loop 1 does the
analogous operation for the 10 mask-only inputs and its own exponent table.
The caller initializes 27 zero coefficients, invokes both loops, prepares
the linear multiplier, reads the coefficient at the configured factor
degree, runs the reverse Horner loop, computes the power-26 branch, and
combines the results.

The proof targets cover the following chain:

* `ExtractedMaskCoefficientArray`, `...Schedule`, and `...Step` specify the
  bounded array-update model, the two finite exponent schedules, and the
  extracted loop-body success/canonicality contracts.
* `ExtractedMaskForwardRange` and `...CoefficientLoop0/1` establish the actual
  forward iterator and each full bounded loop's execution against its
  symbolic write model. `...CoefficientDecode` and `...CoefficientWriteMeaning`
  turn those updates into exact coefficient-cell values.
* `...CoefficientLoopMeaning` combines the intervals, while
  `...CoefficientScheduledSum` reindexes the polynomial coefficient sum.
  The final schedule facts say the two schedules are disjoint and cover the
  27 cells except cell 23; `...PopulatedMeaning` proves that the exceptional
  cell remains zero and that the completed coefficient polynomial is the
  scheduled sum.
* `...LinearsExact`, `...Constants`, and `...CallerModel` compose the generated
  selected-mask caller. Under the stated canonical-input hypotheses (16 C1
  values, 10 mask-only values, the 10 point values, and explicit `g`), the
  caller succeeds, its output is canonical, and its exact decoded result is
  the scheduled polynomial at the first linear value plus
  `(1 + linear16^26) * g`.
* `...LinearMap` proves that the local mask-linear expression commutes with
  an arbitrary ring homomorphism. It does not select or prove the concrete
  homomorphism from the exact tower into `WideExact`.

The final theorem statements retain canonicality of the source values as
explicit hypotheses. The proofs derive loop/index success, intermediate
canonicality, table reads, array updates, and constant facts from the
component contracts; they do not assume that the generated caller has already
succeeded or that it returned a desired output. The final callers' theorem
does not add an acceptance premise.

For the requested change audit, I compared the initial reviewed snapshots to
their selected final green snapshots for CallerModel, the coefficient step,
ScheduledSum, coefficient write meaning, and coefficient loop meaning. The
CallerModel diff changes only initial-array canonicality simp plumbing,
explicit range-bound proofs, and explicit rewrites of the already-proved
add/multiply result equations. The coefficient-step diff changes list/array
index proof plumbing and names the exact exponent-table cell used as the
destination; its success/canonicality/update conclusions are unchanged.
ScheduledSum only makes its `Fin 27` schedule universe explicit and derives
the same zero-at-23 fact from the existing exception-cell premise. The
write-meaning diff supplies explicit bounds for the same table lookups and
their representation equality. The loop-meaning diff adjusts induction
argument order and finite-index arithmetic. In all these comparisons, the
definition-level data flow, loop bounds, table schedules, canonicality
premises, and result equations remain the same; no new proof premise or
alternate coefficient model appears in the final versions.

The source annotations and extraction input pins associate the generated
declarations with the pinned Rust source. The Lean results prove facts about
the generated Aeneas declarations and their exact symbolic models. This
batch alone does not prove that the Rust compiler/runtime behavior refines
those declarations, nor does it prove a transaction acceptance, privacy,
security, or end-to-end semantic claim. The separate field-hom/basis
compatibility bridge is not part of these 15 checked targets.

## Final target and object pins

All rows below refer to the successful receipt named in the attempt column;
the complete receipts, axiom outputs, direct-import pins and source snapshots
remain in the offload attempt directories. Source SHA equals that successful
attempt's `source_sha256` and snapshot hash.

| Target | Attempt | Source SHA-256 | Object SHA-256 |
|---|---|---|---|
| `ExtractedMaskCoefficientArray` | `coefficient-array-b` | `af0766e6434158f262db760dc80dfc5b17556fafc66a20842b60bb98869ce313` | `d9046eb020d349eb7a1ee5b5867044d9cb1dd0167725447f4a6ea8d09798d8ce` |
| `ExtractedMaskCoefficientSchedule` | `coefficient-schedule-d` | `da369c57556aaa58a14c5a557d56a54c09f682aa2800ac8b8ea52882f14f2c39` | `bf9ea6cd9bbb3917b8cb9c24d3fc5ce9cab621ce0885e178d7bb9de5bb73baa7` |
| `ExtractedMaskCoefficientStep` | `coefficient-step-c` | `833fc56d40cc09a3e411172570cb54b8fe5f6c1c5055bccfe4447ac16f231eb4` | `fe9cbe7ff2979243e73d7611c6b72395948e06a787f476bba50639d350862dc3` |
| `ExtractedMaskForwardRange` | `forward-range-e` | `a05795b512b963be960ae42355e283a153f1cc6426604029ce71f76a3468bc47` | `c8d71665bdb439f08a67e04ca12f37e3c371402b17fcec8599c7d09a4f9f7d3d` |
| `ExtractedMaskCoefficientLoop0` | `coefficient-loop0-g` | `9d2fd5377939051a988b6faeb31ed95aee22aa98fdfda779f373c94877bfa1b6` | `36216956c863bf7a684fb970edb9649945650524e104ffe7654dabeb5e12c9e9` |
| `ExtractedMaskCoefficientLoop1` | `coefficient-loop1-b` | `cdf4a640b48a1a1e41cdd4853d7aa76dd00d70ecf7450beafeea1597934f766c` | `719f269f32edb79e7ade55eeee8396c5c7852272a6b205743588267d9483785b` |
| `ExtractedMaskLinearsExact` | `linears-exact-c` | `e0394ca0a98ebcb6b9e99510dd003cac0d8a202d5538110a43c28998d5b2e804` | `5a7dd621bcf8d0be6ae6c9c73220629f458fdbfe4e14adfc95fc9e54c5c88e45` |
| `ExtractedMaskConstants` | `constants-b` | `3d2bedd4b3dbda6b2d7a9fe80b2b7756c7bec99137637021eb4d2031b73c90d2` | `41fc8c7afbf143a67b2613034e3f63924c33155f122ede463b03c7abd859036b` |
| `ExtractedMaskCallerModel` | `caller-model-h` | `4e675d196e7d3c281674d440aa8d92c554cc9d29249cb2ad0e85d27121d12e1c` | `5c9fdf5d1634d3731c3b6344b2947990c0fee51ec677f33374b881f79678c631` |
| `ExtractedMaskCoefficientDecode` | `coefficient-decode-d` | `66dcc633180daad7237590145f39d3e86e607aff013908920c3468a469f8f6ec` | `df569da81be274337760b096c75c0f46a57e6b890f4e14e6aea7200829d5f991` |
| `ExtractedMaskCoefficientScheduledSum` | `coefficient-scheduled-sum-c` | `fa2381c53dbe7a74a59a39d32db6ef80f4e45d83bf64a0c696be9cb68420ca93` | `b38da5be0de05131ae944892a08248941ca543d916a44843190cdba5678da00b` |
| `ExtractedMaskCoefficientWriteMeaning` | `coefficient-write-meaning-c` | `134f65211b0b283e248c5db3d9ee04576fa6c803de630b103e4d10a5e0b40ad5` | `60ec8a7cf873c6dced451852fe68b638bdd3ca72365d1297284189be73932769` |
| `ExtractedMaskCoefficientLoopMeaning` | `coefficient-loop-meaning-c` | `c06ff269b6efda7bb8e81c1335592ab060a4c12cd9c6d64cb40284134019d790` | `9c2163523a031783e9bbb1bbbab44442e2a8958e42d9ac15e44579e7751f03b4` |
| `ExtractedMaskPopulatedMeaning` | `populated-meaning-i` | `6e5a317e633b1eeb09395a7137425a5ed3c647c608227783f69ffb870232b6db` | `90036441d3097d1c8e846fed922d68e71f76ebfad07136cb27531b23783a4190` |
| `ExtractedMaskLinearMap` | `linear-map-a` | `4c58b1c474aa22ac45c8d02b517a47360594820a7ba2234992293f0cc10b385e` | `a548c9ced431163e8b4d0ea135488001b1d320414b911344d917e29d6351f50f` |

## Provenance gate suggestion

For future focused targets, require every imported Lean object to have a
matching successful source/object receipt in the same evidence set (or an
explicitly pinned, independently checked external-cache provenance record).
At runner preflight, verify both the imported object's SHA and the source SHA
recorded for the build that produced that object; do not infer their pairing
from a mutable shared `sources/` path. Preserve an immutable snapshot per
successful compile. This catches the CallerModel discrepancy above without
forcing a rebuild when the object and its successful producing receipt are
already retained.
