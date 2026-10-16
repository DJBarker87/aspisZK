# Mask bridge dependency evidence reconciliation

The 144-target focused queue is complete on the pinned Lean 4.32 kernel.
This replaces missing source-to-output evidence for historical dependencies
used by the extracted mask bridges. It is a dependency compilation checkpoint;
it does not prove the complete accepted-verifier or private-spend theorem.

The queue was justified by missing evidence: 80 historical modules had
successful source receipts without an output hash, 22 had source/object pins
only, and 42 additional project dependencies were discovered in the concrete
bridge's import closure. Existing successful, output-bound evidence was reused.
This was not a package-wide regression or a rebuild of Mathlib/Aeneas.

## Checked result

The [evidence bundle](../evidence/mask-provenance-reconciliation-20261016/README.md)
contains 152 retained attempt directories, including failed attempts, and
1,234 archive members. Every one of the 144 selected successful attempts has
an exact source snapshot, exit status, wall time, peak RSS, swap count,
direct-import pins, output hash and axiom-report record. Compiled objects
remain in the pinned NUC workspace; their hashes and paths are recorded.

- 144 successful targets; maximum process RSS 3,573,252 KiB; zero process swaps.
- 806 emitted axiom reports: 801 use only `propext`, `Classical.choice` and/or
  `Quot.sound`; five use no axioms. There are no custom axioms or `sorryAx` in
  those reports.
- Eleven modules emit no axiom reports. Their compilation passed, but they are
  not counted as audited declarations.
- All 351 recorded direct-import object edges match the current cache; no
  current source-pin mismatch was found.
- The lead independently checked every archive member, all 144 selected
  source/receipt pairs, the raw-log axiom reports, and all 144 current output
  hashes over SSH. See [the lead review](../evidence/mask-provenance-reconciliation-20261016/root-review.json).

Successful-target controller times sum to 300.863 seconds. This is the sum of
the selected compile attempts, not the elapsed research or evidence-collection
time. Jobs ran serially, with 4 GiB MemoryHigh, 6 GiB MemoryMax and zero swap.

## Two proof repairs

`AspisV8R19.UniformStateFirstHit` now explicitly imports the rational ordered
field instances and proves the denominator nonnegative symbolically. This
replaces unavailable tactic/import behavior; it does not normalize `256^32`.
Its final source SHA-256 is
`75160419184f20aee9645b1da3ccda18e32e5b28a118fdc45ec1d5d26de129d2`.

`AspisFormal.V6PublishedTheoremInterfaces.output_list_expression_lt_113`
keeps `sqrt(outputRate)` as one algebraic quantity, squares a nonnegative
inequality explicitly, and discharges the resulting rational contradiction.
Its final source SHA-256 is
`904f5e5b9b6b38b7b3009cbe755ae90c692cb88c2aa303f1abf3c212a152a37c`.

Both theorem statements and premises are unchanged. The original frozen
sources, failed attempts and successful replacement snapshots are retained.
Checking a historical module containing work-normalized statements does not
adopt those statements as the current security target: the target remains
100-bit per-attempt soundness without grinding credit.

## Scope still open

The generic and concrete mask bridges passed their
[focused dependent rechecks](../evidence/mask-final-bridges-row-model-20261016/README.md)
against the newly reconciled objects, with three standard-only axiom reports.
Accepted-input canonicality, actual verifier-to-relation
composition, efficient extraction, privacy, source/runtime correspondence
and final settlement/artifact gates remain open. This evidence does not turn
conditional protocol statements into an unconditional security theorem.
