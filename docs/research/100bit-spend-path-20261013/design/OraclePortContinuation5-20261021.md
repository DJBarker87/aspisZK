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

Five new modules complete the **byte-model checkpoint composition**:

- `OraclePortCheckpointAbiC5` serializes every field in the frozen order,
  proves every block width, 1736-byte body and 1768-byte total size, and
  binds the checksum to that body.
- `OraclePortCheckpointSlicesC5` proves the exact physical slice for every
  prepared and accumulator field. Its extraction proof is structural in
  the 18-field list, never in a concrete encoded vector.
- `OraclePortCheckpointPreparedC5` decodes state, both roots, all challenges,
  the 22 queries, ten semantic challenges, four circle coordinates and claim
  from those slices, proving a complete prepared-value roundtrip. The
  four-byte query codec is proved symbolically in the encoded numeral.
- `OraclePortCheckpointResumeC5.save` retains the same stored proof bytes
  alongside the checkpoint and writes the **computed ten-step accumulator**.
  `decode_written` reads rhs, power and all 64 weights back from their actual
  byte ranges; it accepts no externally supplied saved accumulator.
  `physical_resume` gives the full 22-step state after twelve resumed steps;
  `physical_finish` identifies its finish equation with R14's ClosedSum.
- `OraclePortCheckpointOracleC5` makes all hash calls explicit as Program
  reads: three on write and three on resume. `writeResume_value` decodes the
  prepared fields and accumulator from the saved bytes and returns the
  22-query state. `writeResume_reads` proves exactly six issued hash reads.
  The writer creates the oracle-dependent checkpoint inside the program,
  rather than accepting it as a supposedly fixed experiment input.

| Byte range | Bound model field |
|---|---|
| 0–16 | Magic, S2, saved next=10, reserved bytes |
| 16–48 / 48–80 | Hash of retained stored proof / public bytes |
| 80–112 / 112–176 | Duplex state / two roots |
| 176–304 | gamma, kappa, alpha0, alpha1 |
| 304–320 / 320–408 | rho / 22 little-endian query indices |
| 408–568 / 568–632 | Ten semantic challenges / two (x,y) points |
| 632–664 | Prepared claim |
| 664–696 / 696–712 / 712–1736 | Reached-ten rhs / power / 64 weights |
| 1736–1768 | Hash of domain ++ complete body |

The selected matching data supplies gamma/kappa/alpha; the checkpoint
context still supplies the state, roots, semantic challenges, coordinates
and claim. Connecting that context and the recomputed matching data to the
actual accepted parsed transcript is not inferred from codec roundtrip.
No result identifies this mathematical decoder with frozen Rust or supplies
Pool caller/policy provenance. The proof is about authentic save outputs;
a self-consistent unkeyed checksum is not represented as TX1 provenance.
`Context` is explicit, not hidden in a newly named completed dV.

All five final modules compile with standard axioms. Local elaboration
failures (including accidental recurrence unfolding during definitional
comparison) are retained. The replacement proofs make recurrence operators
opaque and apply the already-proved symbolic state law; no cap, heartbeat
or recursion limit was raised.
