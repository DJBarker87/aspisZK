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
The mathematical prepared decoder enforces per-query bounds, but does not
include frozen `validate_checkpoint_queries`' duplicate-query rejection;
its roundtrip is intentionally defined for every model query vector.
Consequently it is not a total refinement of the Rust resume parser, and a
frozen-parser join must establish query uniqueness and the other caller
guards rather than infer them from the model roundtrip.

All five final modules compile with standard axioms. Local elaboration
failures (including accidental recurrence unfolding during definitional
comparison) are retained. The replacement proofs make recurrence operators
opaque and apply the already-proved symbolic state law; no cap, heartbeat
or recursion limit was raised.

## Stage 3: endpoint comparison and the dependent obstruction

The requested completed-dV headline is **not proved**. Stage 1 stops the
proposed whole-row equality inference; substituting that equality into
Checks would be unsound. The counterexample does not prove that no other
selected-observation transport can work. It identifies the exact required
replacement proof. No definition is renamed dV merely because its parser,
checkpoint codec and candidate-row arithmetic checks pass.

In particular, the semantic reader retains a C2-word callback inside its
semantic messages. Equality of query-fibre arithmetic alone is not yet a
proof that its claim/polynomial/equation observations transport. Completing
this requires a new reader-invariance proof, followed by instantiation of
C4's indexed recovery with the actual containing trace, three root frames,
budget and collision exclusion. Changing the annotation compiler to the
candidate's query-dependent sparse completion would require a fresh
causality argument; it is not a harmless equality rewrite.

Comparison source: `research` at
`4f3df75f58b1b4f9ea9d26139a1ab46990bef7bb`, pinned in the evidence. Its
SOUNDNESS-HEADLINE document contains **v2 and v3**. V2 fixes the concrete
M10 extractor/parameters and removes ledger/uniformity premises. V3 also
removes its recorded-log-length premise for the existing pure-decision
experiment. Those results are respected, not re-proved or modified here.

| Headline v2 item | This draft's exact result | Remaining before a completed-dV endpoint | Premise deletion here |
|---|---|---|---|
| `d : ErasedPrefix → ErasedMessage → Bool` | Specified stored-byte arithmetic candidate, oracle Program decision; retained adaptive input and exact logical replay from C4 | Complete selected-reader acceptance and join the physical checkpoint program to the accepted source context; a new carrier is an interface change | None |
| `h_R16_instance` (collision-free accepted instance) | C4 constructs instances in the new admitted/canonical stored experiment | Instantiate at a completed decision with all input/context identities | None |
| `h_R13` (reader equals selected source data) | C4 binds source choice to compiled reader; authenticates exact selected opening indices | Instantiate actual-run recovery and prove selected-observation transport; full-word/row equality does not follow from selected recovery | None |
| `h_R15_writer` (all 22 first matches) | Candidate-row checked first matches; decoded physical ten/twelve accumulator composition | Transfer candidate data to actual compiler reader; retain matching-state/source and runtime joins | None |
| `h_R3_semantic` | Candidate checks EquationEndpoint; C4 proves terminal independence of W/V | Full semantic-reader/C2-callback observation invariance and actual compiled-row instantiation | None |
| `h_R14_backend` | Candidate pairing and ClosedSum; C5 decoded physical finish is exactly model ClosedSum | Bind reconstructed matching data and Context to reached parser/source; frozen arithmetic/caller refinements | None |
| `h_Rwire_tag` | Existing candidate guard/header and previous logical framing facts unchanged | Completed-decision checked format/tag composition | None |
| TX1 / Pool TX2 failure model | C4 stored identity and accepted logical replay; C5 authentic physical byte-model save/resume with six explicit hash reads | Connect the two constructions and the frozen runtime caller, account, policy and source-data provenance | None |
| M10 concrete extractor and parameters | Unchanged; v2 closure remains the other worker's result | New stored-carrier probability/cost composition must use its own justified budgets | None |
| `h_M10_log_length` (v2 only) | C4 conservative bound Q+2322 for the new recorded carrier; v3 deletes its old-experiment premise | Do not substitute the new conservative bound into v2's Q+1161 binder or pretend v3 covers a different experiment | None |
| Numeric deployed-failure conclusion | Existing headline left byte-identical | New stored-experiment soundness/transport theorem at a completed dV | None |

The retained before/after v2 source snapshots are identical, as are the
R19 endpoint snapshots. Both signature diffs are empty: **zero claimed
premise removals or replacements**. They are preservation evidence, not a
deletion-only specialization that has not actually been proved. No draft
headline at `dO := dV` is advertised.

## Evidence freeze

`OraclePortContinuation5Manifest.json` records 19 focused attempts, six
successful final modules and 38 final theorem axiom reports. Eight attempts
succeeded (including intermediate source versions); eleven failed with
retained local errors. Every final theorem uses only a subset of
`[propext, Classical.choice, Quot.sound]`. Peak RSS was 3,654,221,824 bytes;
all attempts reported zero swaps. Each receipt includes exact command,
source revision/hash, import hashes and dependency/environment fingerprint,
exit, wall time, RSS, swap, complete axiom lines and errors. No unchanged
source/dependency attempt was repeated.

The audit verifies all receipt/source snapshots, every final source and
import-object hash, theorem coverage, standard axioms, the new-module-only
scope, and unchanged endpoint signatures. Failed attempts may contain
Lean's error-generated `sorryAx` reports; none occur in successful results.
No full release manifest is replayed at an unfinished endpoint.

```sh
python3 -B docs/research/100bit-spend-path-20261013/evidence/oracle-port-draft-20261021/OraclePortContinuation5Audit.py
```

No shipped source, existing Lean module, candidate re-pin, M10 file, key or
deployed artifact was changed. Commits stay on the unmerged draft branch;
no push or merge was performed.
