# Oracle port continuation 5

Unmerged draft; only new OraclePort Lean modules are changed.

## Stage 1: selected recovery and row equality

The proposed inference from exact indexed recovery to equality of the two
literal row families is invalid without another argument about unqueried
coordinates. `OraclePortSelectedRowObstructionC5.unselected_exists` proves
for **every** 22-query vector that some final-word coordinate is outside all
88 selected folded-fibre positions. This is cardinality transport over
`Fin 22 × Fin 4`, not evaluation of the full word universe.
`selected_fibres_do_not_determine_rows` changes that coordinate by one while
preserving C1, C2, and every selected folded fibre. `row_different` shows
that row 30 can retain equal erased bytes and unequal literal messages.

This disproves the inference from selected metadata agreement, not the
stronger claim that there exists an accepted collision-free execution with
these specific words. It does not manufacture an accepted run. The actual
compiler recovers full maps from the original log; the prover can pre-read
additional leaves. The candidate instead completes all nonselected leaves
with the typed zero default. No existing theorem excludes those extra reads.
Collision exclusion authenticates recovered values; it does not delete them.

Accordingly, whole-row rewriting is stopped. The viable replacement is
transport of reader/check observations under selected-fibre agreement,
including the semantic reader's C2 callback. The previous local arithmetic
lemmas remain valid. CheckedAcceptance on compiler rows is not yet derived.

Attempts 1–3 are retained under the evidence directory. Attempt 1 had local
elaboration/type errors; attempt 2 proved the single-fibre example; attempt 3
adds the general cardinality theorem. Final five axiom reports contain only
standard axioms. No unchanged compile was repeated.

## Stage 2: physical checkpoint composition

In progress. The serializer must bind the frozen 1768-byte field ranges to
the reached ten-step state; an unkeyed checksum alone is not provenance.
