# Parser and multiproof source refinement

Assigned continuation branch: `codex/cx-multiproof-cone2-20261021` (prior packet: `codex/cx-multiproof-cone-20261021`). The oracle-decision port
is approved for this work. Target: `OraclePortHeadlineFrozen` at
`OraclePortFrozenOrder.dV_frozen`, not the superseded recursive schedule.

## Stages

1. Pin actual parser, compact codec, leaf-batch and binary-level source cuts.
   Keep shipped files unchanged. Generate proof-only copies with an explicit
   substitution ledger; compare owned transitions under Kani.
2. Extract owned references using pinned Charon/Aeneas, preserving row and
   level recursion. Prove their mathematical meaning in new Lean modules.
3. Compose through height 18, parser sections and the reached caller, retaining
   ordered oracle addresses and ordinary rejection. Audit the exact residual
   before changing the cone classifications.

## Proof boundary

A passing one-step certificate is not a whole-loop certificate. Equality of
roots is not equality of ordered oracle logs. The scratch suffix and writes
made before rejection must be retained where observable in the source cut.
The global `AcceptedRunJoin` still requires the other cones and the frozen
source/model caller identities. No whole cone is declared complete here yet.

## Resources and evidence

Host workspace: `/home/dombarker/project-offloads/codex-cx-multiproof-cone-20261021`.
Host jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 after
reservation preflight. Rust gates are optimized. Local Lean uses one process,
the shared mkdir lock, `-j1 -M4400 -DElab.async=false`, and a private object
folder. Every compile/proof attempt records target, revision, source/dependency
hashes, exit, wall time, RSS, swaps, and axioms (N/A for Rust).

## Owned reference and first focused proofs

The source-cut generator and all references are proof-only. No shipped crate
was edited. The original conditional tuple in binary_step failed Aeneas borrow
collapse at InterpBorrows.ml:2731; the replacement returns through an owned
write helper. Conversion unwraps were removed to avoid Formatter. The full
parser's first translation exposed external slice/array equality and Vec.extend;
its replacement uses explicit header bytes and an owned row accumulator.

The binary reference translates and its generated Types/Funs compile.
`MultiproofConeCodec` proves total strict-word evaluation, exact agreement
with `OraclePortCompactDraft.rowShape` on all reached rows, and exact compact
value expansion with a zero high half. All three axiom reports are standard.
Full parser-to-parseReached equality and the source joins remain open.

Ten parser/key Kani roots passed (parser-local-2: exit 0, 88.527 s,
2,780,960 KiB RSS, zero swaps). These are primitive predicates/offsets,
not the complete scanner or Prefix caller. Subsequent reference changes
require current dependent certificates. Native-1 passed; native-2 exposed
a missing Debug derive on the proof-only copied error carrier.

Multiproof-step-1 diagnosed memcmp unwinding. Step-2 was stopped to use
arbitrary independent observation coordinates. Step-3 proved leaf insertion
and missing-sibling rejection, but the sibling group timed out at 240s;
the suite was stopped after that diagnosis. Step-4 observes one universally
arbitrary oracle-input byte instead of constructing a full event buffer;
call count and all component lengths remain checked. The complete certificate
is pending. No intermediate check is a whole-cone AcceptedRunJoin.

## Current local step certificates and recursive reference facts

The general symbolic roots now pass; ordinal diagnostic roots have been
removed. Final certificates retain arbitrary arrays, n/i/w and node cursors,
not merely a preflight at i=0. The verified `read32` contract requires exactly
32 bytes and equates every returned byte to its input. `binary_sibling_group`
uses only that verified stub. Callback observations check every component
length, call count and a universally arbitrary address-byte coordinate; the
returned digest and scratch are checked at universally arbitrary coordinates.
No entire tree is unrolled by Kani.

* `multiproof-current-1`: all five roots pass, exit 0, 80.283 s,
  741,520 KiB peak RSS, zero swaps.
* `parser-current-1`: all ten field/key roots pass, exit 0, 48.538 s,
  3,291,276 KiB peak RSS, zero swaps.
* `leaf-layout-2`: three roots pass, exit 0, 15.164 s, 563,692 KiB
  peak RSS, zero swaps. The count-group body is generated from the actual
  node_count loop with Arity::Two fixed and its reference qualifier adapted.
* `native-3`: all four optimized differential tests pass, including full
  accepted binary verification, partial rejection scratch and the complete
  compact parser under framing/canonical/salt/root/node mutations.

The failed Kissat/JSON runs are retained. The last diagnostic preflight
reached MemoryHigh throttling in the Kani driver (not an OOM or cap increase);
it was stopped. Borrowed observation buffers, verified byte-reader stubbing,
CaDiCaL and text output resolved the general symbolic cases. Assertion
reachability cover checks are disabled in these final runs; correctness,
bounds, overflow, explicit contract preconditions and unwinding checks remain
enabled. Nonempty witness domains are n=2,i=w=at=0,idx=[0,1,...] for the
occupied case; n=1,i=w=at=0 with 32 sibling bytes or zero bytes for the sibling
and short cases. Array contents and observation coordinates remain symbolic.

`MultiproofConeLeaf.leaf_step_total` proves outer-success of the actual
extracted insertion whenever n<16, retaining inner unequal-duplicate failure.
`digest_eq_total` proves exact 32-byte equality. `MultiproofConeWordScan`
proves total checked word scanning against a structural list recurrence on
arbitrary input lengths. `MultiproofConeHeight.height_total` inducts over the
actual extracted height recursion up to 18; its RowJoin still needs the
concrete frontier/scratch invariant. Its conclusion concerns returned values,
not source log equality. These are standard-axiom focused facts, not whole
source-cone joins.

The complete compact parser reference now translates without any generated
external declarations; its Types/Funs compile. The reference source differs
from the retained binary extraction only by cfg(kani) reader-contract
attributes, which are absent in extraction builds. A final combined run is
needed after adding the exact count-group/leaf source cuts.

## Final focused verification

The combined 18-cut run is current at Rust revision
`e0251ff98a99402ff34d19c1d8cd4558aa59d887`: exit 0, wall
154.0682397610508 s, peak RSS 3,290,456 KiB, zero swaps. Every root uses
the final committed Rust files, and the source/solver/limits are in the receipt.
`native-final-1` records the four optimized differential tests on those same
final Rust files. No shipped file or sibling candidate changed, so the
conditional SBF/ELF rebuild requirement was not triggered. No frozen ELF
byte-identity measurement is claimed.

All eleven new Lean modules compile, with thirteen authored theorem
declarations (including two private helpers) and 27 current standard-axiom
reports including the final import audit. The final target
`MultiproofConeFreeze`, attempt 1, exited 0 in 22.041078709065914 s with
3,554,918,400-byte RSS and zero swaps, at source revision
`e0251ff98a99402ff34d19c1d8cd4558aa59d887`; its source SHA and direct
import fingerprint are in the receipt. It imports the unchanged frozen
headline and reports its axioms as well as both complete owned reference
entry functions. `MultiproofConeHeader.header_total` handles every stored
slice, including short inputs, and matches `OraclePortHeader.accepts`.
The endian lemmas reuse the retained all-input parser, including rejection.

One queued word-scan attempt was refused before starting Lean after its
source changed while waiting. Its metrics are explicitly not applicable,
and it is excluded from kernel evidence. Other failed receipts are retained
for elaboration, the corrected heartbeat-expensive header proof and missing
cache imports; they are never current evidence. The header replacement uses
a generic Boolean/Result lemma rather than raising any limit. No job hit a
Lean memory cap.

The retained endian proof needed two diagnosed missing cache namespaces,
AspisV8R19.SamplerWordBridge and AspisR72Sampler.Funs. A task-private union
of 67 hash-pinned object/companion symlinks supplies them. No shared object
was overwritten or rebuilt. The union and all selected direct imports are
recorded. This is a focused compatible import audit, not a coherent frozen
release manifest replay.

## Unfinished whole-cone obligations

**Neither requested whole-cone accepted-run join is discharged.** No premise
is deleted, no source implementation is adopted, and no whole verifier
`AcceptedRunJoin` is constructed. The design rows retain whole-cone (d).

For the parser, prove semantic row/Vec expansion, then bind stored bytes to the actual reached
projection/decoder. Local totality does not prove the entire caller equation.
For the multiproof, instantiate the exact live-prefix/scratch relation and
RowJoin, establish key sorting/tie order and leaf/count/padding loop
simulations, and prove the ordered source digest log and both batch callers.
The extracted reference returns values/state, not an instrumented whole-run
log; `height_total` therefore cannot discharge log equality on its own. The
Kani one-call byte/count observations support the P6 local cuts, not the
missing complete ordered caller/annotation proof.

Reproduce the source and evidence checks with:

```sh
python3 -B tools/multiproof-cone-20261021/generate.py --check
python3 -B tools/multiproof-cone-20261021/audit.py
```

`audit-result.json` deliberately records both complete-cone fields and
`accepted_run_join_constructed` as false. The frozen headline/R19 and all
Session A and sibling source modules remain byte-identical to this task's base.

## Stage 5: complete strict scanner (2026-10-21)

`MultiproofConeStrictScan.scan_total` identifies the actual Aeneas-extracted
owned parser scanner with `OraclePortCompactDraft.scan` for every 57,607-byte
slice, including rejection. Its proof composes arbitrary-byte canonical-word,
compact-value and slice lemmas with an induction over the 22 opening records.
`MultiproofConeCanonical.scan_total` establishes exact frozen canonicality,
not just structural word checks; `MultiproofConeCompactScan.check_values_total`
establishes it for every 16-byte-aligned compact region. The scanner theorem
adds no source acceptance, canonical-input or honest-run hypothesis.

The corresponding focused receipts record all section 6 fields and standard
axioms. This is reference-to-model scanner closure, not the complete parser
or either requested accepted-run join. Semantic rows, expansion and reached
caller binding remain open. The preceding `audit-result.json` records the
11-module/18-cut committed checkpoint; the expanded packet is being audited
in the following stage.

A nineteenth P6 root, `semantic_zero_high_field`, checks the frozen semantic
field validator on each arbitrary zero-high compact expansion against the
owned compact predicate. Its single focused host gate passed (0.638571 s,
186568 KiB peak RSS, zero swaps); the receipt pins actual working source
hashes. The recorded base revision predates this added root; a new complete
19-root gate against a committed revision is required before final audit.
Only proof-tool copies changed; all shipped source files remain unchanged.

## Stage 6: total compact expansion and frame operations

`MultiproofConeExpansion.expand_total` proves the actual extracted owned
expansion recurrence returns precisely the frozen `expand` bytes for every
16-byte-aligned input satisfying the independent vector-capacity bound.
`MultiproofConeExpansionLength.empty_accumulator` additionally proves exact
doubled output length. The proof uses length induction and the checked
single-value expansion, never reduction of a concrete expanded proof.

`MultiproofConeFrameModel.header_model_total` identifies the five checked
header reads/comparisons with the exact frozen tag and `le32` frame.
`MultiproofConeLogicalPayload.good_total` and `bad_rejected` cover canonical
rejection, compact expansion and ordinary payload copying.
`MultiproofConeRowScalars.scalars_total` supplies all reached table, division,
offset and next-row checks. `MultiproofConeFrameBuild.framing_total` supplies
frame allocation/push and the exact decoded accumulator append, under size
bounds independently established by these preceding facts.

`MultiproofConeParserControl.parse_of_rows` checks complete top-level parser
control for every input length, retaining the explicit **uninstantiated**
`RowsJoin` hypothesis. The extracted row normalization and row-count induction
are the next targets. No whole parser/source accepted-run join follows from
this conditional theorem. Multiproof RowJoin and ordered-log/caller obligations
remain unchanged and open.

The expanded P6 gate now pins committed Rust revision `c2beabcc1`: 18 ordinary
roots passed in 186.193180 seconds (3,288,384 KiB peak RSS); the separately
selected verified `read32` contract passed in 0.910352 seconds (177,052 KiB).
All 19 roots have zero swaps and recorded 6G/8G/no-swap/64-task scopes. Their
preflights reserved 16 GiB and 32 GiB respectively after adding our scope,
below the 55 GiB limit. No unchanged full Kani suite was repeated to add the
omitted contract selector. Native tests are reused from the preceding runtime
checkpoint; only proof-tool visibility and an added proof root changed.

Failed proof/elaboration attempts remain recorded. The frame-size cast was
made symbolic to avoid reducing abstract usize width. An unsuccessful broad
simp over the library's irreducible recursive `toLEBytes` hit the default
recursion limit; it was replaced by a named cast lemma, a byte-list projection
lemma and four explicit small-byte steps. No limits were raised. Successful
current theorems have standard axioms only. The earlier audit-result remains
the preceding checkpoint; final expanded packet auditing follows row closure.

## Stage 7: complete owned parser reference (2026-10-21)

`MultiproofConeSemanticRows.rows_total` proves the actual extracted owned
row recurrence against `OraclePortCompactDraft.semanticRows`, by row-count
induction. It preserves the decoded accumulator and every ordinary rejection.
The initial-domain instance `MultiproofConeParserTotal.rows_join` discharges
RowsJoin; `parse_total` now has **no** RowsJoin, canonical-input, honest-run or
successful-source antecedent and covers every `Slice U8`. The result compares
the Option semantic-row projection, including rejection. `accepted_parse`
identifies the successful frozen Parsed value, its wire bytes and semantic
rows. This is total **owned-reference-to-model** refinement, not exact equality
of every production Rust Error payload and not production source adoption.

The main row induction passed in 17.006464 s, 3,604,381,696-byte peak RSS;
the complete parser bridge passed in 20.897470 s, 3,512,582,144-byte peak RSS.
Both have zero swaps and standard axioms only. The extracted single-row
normalization passed independently first. The new row proof reconstructs its
local scalar, slice and vector bounds from the row count/table; it does not
assume the desired loop equation. No concrete 27-row wire was unfolded.

The printed tuple let was an Aeneas `uncurry` application. Its explicit
unfolding, followed by checked bind congruence with the actual continuation,
resolved the row normalization. One proof-local elaboration transparency
setting permits ordinary unfolding of implicit scalar bounds; it changes no
kernel axiom and raises no resource or proof limit.

**Both whole production source-cone joins remain open.** Parser production
P6 control/loop composition and stored-to-reached/decoder binding still need
adoption. Multiproof live-array/row/log/caller joins still need discharge.
The checked parser reference does not instantiate the complete source
AcceptedRunJoin or lower its target.

A whole-prefix sort BMC attempt is retained as **INCOMPLETE** despite its zero
raw driver exit and misleading success summary: it has zero completed
VERIFICATION SUCCESSFUL results and stops during symbolic unwinding near the
240 s harness timeout. Its assessment and exact failed harness snapshot are
under host/receipts/batch-sort-1. This is not a mathematical counterexample or
a verified result. The existing 19 roots were separately checked to have 19
completed solver results. The runner/auditor is being hardened to fail closed;
sorting is being replaced by an exact insertion-iteration cut and owned row
recursion, at the same memory cap. No unchanged larger-cap rerun is planned.

## Continuation stage 1: sort and insertion closed (2026-10-21)

The WIP `MultiproofConeSortStep.insert_step_total` already checked successfully
in retained attempt 3. The new `MultiproofConeSortPermutation.insert_step_perm`
proves unconditional whole-array `List.Perm` for that same atomic transition.
`MultiproofConeSortInsertion.insert_rows_total` proves totality of the actual
extracted right-to-left insertion recurrence, exact content and untouched
arbitrary scratch suffix, without sortedness. `insertReverse_perm` and
`insertReverse_sorted` give its multiset and order laws.

`MultiproofConeSortTotal.sort_rows_total` proves the complete extracted outer
sort terminates for every n≤16 with an initially sorted processed prefix.
`sort_eq_mergeSort` identifies its result with Lean core mergeSort by
`List.Perm.eq_of_pairwise`; the suffix beyond n is unchanged.
`MultiproofConeSortOrder.packed_order` proves exact index/position tie order,
and `sorted_positions` identifies the returned packed prefix with the frozen
`sortedPositions` construction, assuming only the independently specified
initial batch-key prefix. `source_start_one` connects the Rust 1..n start to
the identity zero iteration. No distinct-query assumption is imposed.

All new declarations have individual standard-axiom reports. Exact targets,
source revisions/hashes, import fingerprints, exits, wall/RSS/swaps and logs
are recorded in `manifest.json` and the named module-attempt directories.
The continuation uses a fresh private object directory prepended to the
retained cache; no old/shared object is overwritten. Failed elaboration
attempts are retained, never current evidence. No limit was raised.

The existing `batch-sort-atomic-1` P6 receipt is reused: one completed solver
result, exit 0, 1.548632 s, 176304 KiB RSS, zero swaps. The rejected whole-sort
BMC attempts remain explicitly incomplete. This stage proves sort/reference
meaning; production loop adoption and the remaining multiproof representation,
ordered-log and caller joins are not claimed. No shipped source changed.
