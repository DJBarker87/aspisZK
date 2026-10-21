# Parser and multiproof source refinement

Current continuation branch: `codex/cx-multiproof-cone4-20261021`, base `01b350ddf` (prior continuation branches: cone2 and cone3; original packet: `codex/cx-multiproof-cone-20261021`). The oracle-decision port
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

## Continuation stage 2: leaf step checked; binary adoption blocked

`cone2-leaf-2` verifies both `adoption_leaf_hash_contract` and
`adoption_leaf_batch_step`: two completed solver results, exit 0, wall
33.363419 s, peak RSS 2,720,936 KiB, zero swaps. The caller uses the verified
leaf-hash stub, whose returned digest, component lengths, arbitrary event byte
and exact call count are specified without hidden global state. The source cut
is the entire candidate.rs leaf iteration: key read, cursor increment, selected
opening ordinal, index cast, hash, duplicate comparison and append. All scratch
coordinates, including rejected duplicate scratch, are checked. This proves
that iteration on the supplied opening slice; its stored-proof slice provenance
and the batch caller remain separate. The contract's first caller compilation
failed because the proof-only return carrier lacked `kani::Arbitrary`; that is
fixed, and the failed receipt is retained.

`MultiproofConeLevelIteration.levels_eq_iteration` proves exact full-Result
equality of structural height iteration with the **actual extracted**
`MultiproofConeRef.reference.levels`, for heights through 18. Rejection retains
the exact partial scratch and skips subsequent levels; panic/divergence Results
are retained as well. `iterate_congr_on`/`adopt_eighteen` compose a named local
source equation and successful-level domain preservation over the nonempty,
bounded frontier and physical node slice. Those local source certificates
remain explicit premises. This is a kernel induction, not a claim that the
missing P6 certificate or ordered model-log join is proved in Lean.

The direct complete-level BMC `cone2-level-step-1` timed out with no completed
solver result (241.519697 s, 6,381,040 KiB RSS, zero swaps). Its 512-byte
diagnostic bound also did not cover the entire frozen slot. The replacement
uses a full-state `source_row` contract followed by a composed level harness,
with arbitrary nodes over the complete 5,504-byte maximum slot, arbitrary
scratch/cursors and independent oracle replies by call ordinal. The full-state
contract compares every scratch byte, not an arbitrary-coordinate weakening.
The generated factoring and observation wrappers are documented in
`tools/multiproof-cone-20261021/ADOPTION.md` and the substitution ledger.

The first row-contract gate timed out during propositional reduction after
43,982 VCCs (1,393 remaining after simplification), with zero completed solver
results: 243.280178 s, 6,408,264 KiB RSS, zero swaps. The focused replacement
inlines read32 so unused read bytes can be sliced away, without changing any
postcondition, input domain or memory cap. The replacement also timed out during propositional conversion, with zero
completed results: 243.373072 s, 6,461,112 KiB RSS, zero swaps, 44,201 VCCs
(1,554 after simplification). Neither failure is a counterexample to the
mathematical equality. Both are resource/proof-encoding blockers at this scope.
The dependent composed-level harness must not run or be counted as verified
until the row contract passes. No unchanged larger-cap rerun is authorized or
proposed here. **The complete binary source/reference adoption is not closed.**

The final focused import/axioms anchor is `MultiproofConeContinuationFreeze`,
attempt 1: exit 0, wall 29.013957 s, 3,476,193,280-byte RSS, zero swaps, source
revision `73ea28341`. Its receipt pins the exact source/import hashes and all
fourteen complete standard-axiom reports, including the unchanged headline and
reused complete parser theorem. Every new theorem also has its own report.
This is a compatible focused import audit; no coherent frozen release manifest
was replayed. The prior 19-cut suite, sort-atomic certificate and unchanged
extractions are reused, not rerun. The continuation audit checks the new
proofs and the exact reused leaf-root/callee bodies across the unrelated row
harness attribute change.

No shipped crate, Session A candidate, sibling module, wallet or key changed.
No ELF rebuild was triggered or byte-identity measurement claimed. No headline
premise was removed and neither production cone is reclassified as complete.
Caller lowering was deliberately left to S2. Stop scope: item 1 is complete;
item 2 has a checked leaf step and height induction but remains blocked on the
full-state binary row/level certificate.

Latest check: `python3 -B tools/multiproof-cone-20261021/audit-continuation.py`
validates the new focused proofs, retained extraction pins, exact leaf roots and
callee files, diagnostic dispositions and unchanged shipped/sibling sources.
Its result is `audit-continuation-result.json`; the earlier `audit-result.json`
is the historical checkpoint. Do not run the old all-root auditor as though
the newly added unverified binary roots had passed. All populated-scope
reservation preflights for these host attempts are retained beside the receipts.

Next concrete deliverable: isolate and verify the occupied/sibling/short
full-state row frames and the symbolic node-window read, then run
`adoption_binary_level_composed` with those verified callees. The current
composed harness is an unverified draft. Its input bound and the successful
level-domain postcondition must be retained. A future source change is needed
before another resource-heavy attempt; neither timeout is counted as success.

Receipt provenance: `source_revision` records checkout HEAD when a job starts.
The source snapshots and SHA-256 fields identify the exact tested edits,
including edits not yet committed at that moment; the continuation auditor
checks current source bytes against the successful snapshots. Final reporting
commits do not relabel historical compile evidence as a new release replay.

## Continuation 3: single-node replacement and exact node induction

Branch `codex/cx-multiproof-cone3-20261021`, base `feeb8584a`. The three old
level/row timeouts were not rerun. `cone3-hash-1` verifies the returned-effects
hash observer (one completed result, exit 0, 4.324373 s, 533308 KiB peak RSS).
`cone3-nodes-1` verifies five independent roots: occupied, sibling and short
single-parent steps; exact final-root digest equality; and row domain/progress.
All five complete (exit 0, 64.177020 s, 611548 KiB peak RSS). Both jobs have zero
swaps and recorded 6G/8G/no-swap/64-task scopes and reservation preflights.
They use symbolic scratch, sibling bytes, replies and independent observation
coordinates. No unverified row/level contract is used as a stub.

These are separated 0..32-byte window gates, cursor zero, not a claim to have
verified the entire 5504-byte physical-node buffer. The exact source group is
unchanged. `MultiproofConeNodeWindow.physical_read` proves the checked physical
range and actual extracted read32 return precisely the original sibling bytes,
for arbitrary physical lengths/cursors with enough bytes. `short_iff` proves
the matching short-window condition. The production `.get`/relative-cursor
frame adoption remains a named P6/library-lowering obligation.

`MultiproofConeRead32.read32_total` proves exact byte content. The actual
extracted `binary_step_progress` now proves totality, rejection scratch identity,
unchanged n, successful i advance, w+1 and all next-row bounds, under bounded
frontier/cursor and total hash only. `rows_eq_extracted` proves node iteration
matches the extracted level. `level_preserve` derives nonempty bounded frontier
and physical-cursor preservation for successful levels. `NodeAdoption.eighteen_eq`
composes the local node equation through height 18: the former full-level
certificate and level-preservation hypotheses are removed, while the precise
one-node source equation and hash totality remain explicit. It is exact full
Result/state equality to the extracted reference, not model ordered-log equality.
All current theorem reports use standard axioms; failed elaboration receipts
are retained and excluded from accepted evidence. No limits were raised.

### Exact composition blocker and current endpoint

`MultiproofConeModelBoundary.descending_source` proves that the actual extracted
row hashes an occupied `(1,0)` prefix. `descending_model` proves frozen
`runLevel 2 [(1,v),(0,w)] []` instead returns `(no reads, none)`. Such a scratch
can satisfy the nonempty/bounded/cursor domain: take idx=[1,0,0,...],
n=2, at=0 and an empty physical slice (digest scratch is arbitrary). `paired_iff` proves source XOR
and frozen even/consecutive guards agree under strict ascending order. Thus
promoting the new domain-preservation theorem directly into model RowJoin is
**false** without a stronger invariant. This is not a reached-source bug:
production validates the initial indices, and the invariant must then be proved
through safe overwrites and each parent frontier. No assumption restricting
actual adversarial input is introduced to bypass that obligation.

The requested whole multiproof-cone join is therefore **not established**.
Beyond physical window/frame adoption, the exact missing deliverable is a
sorted live-prefix/scratch-suffix relation maintained by the actual node step,
with matching ordered reads and model `runLevel`, then the initial-key/opening,
leaf/count/padding/root byte/state adapters and both three-slot batches.
`dV_frozen2` invokes the same `verifySlot_frozen` programs in batch0 before
checkpoint and batch1 after resume. No per-cone source signature/implementation
instance, `ConeLogJoin`, or `AcceptedRunJoin` is manufactured. Caller lowering
is excluded and remains with S2.

Before/after premise audit: old `adopt_eighteen` takes an arbitrary *level*
function, a whole-level equation, and successful-level preservation. New
`NodeAdoption.eighteen_eq` takes a *node Step*, defines its level by bounded
iteration, retains one-node equality on RowDomain, and derives level equality
and preservation. It adds explicit `HashTotal`. This is a checked construction
for that source-level carrier, not an unqualified weakening of the old theorem
for arbitrary level functions. The window Kani gates do not alone instantiate
the physical one-node equation. P6 operational/library correspondence and
source/model log/refinement remain proof obligations, not cryptographic axioms.

The current two-transaction headline and its cone consumer were imported in
`MultiproofConeNodeFreeze`, attempt 1: exit 0, 19.014795 s, 3533914112-byte
peak RSS, zero swaps, source revision `e0661080a`. All 14 anchor reports have
standard axioms only. Every new authored theorem also has its own report;
receipts pin exact source hashes, imports, command, revision and metrics.
This is focused compatible cache reuse, not a coherent release replay.
The old 19-root/parser/sort/leaf/runtime evidence is reused for unchanged
executable bodies; no unchanged full regression or failed binary gate ran.

No shipped crate, Session A candidate or sibling module changed. The only
existing generated Rust-body change is proof-copy `root_matches` visibility;
its body remains exact. No frozen ELF rebuild was triggered or identity
measurement claimed. No wallet or key was touched; no push or merge occurred.

Current focused audit:

```sh
python3 -B tools/multiproof-cone-20261021/audit-node.py
```

Its receipt is `audit-node-result.json`. The preceding audits are historical
checkpoints, not claims that the timed-out full-state contracts became verified.

## Continuation 4, stage 1: live-order invariant

`MultiproofConeLiveOrder.step` proves the mathematical in-place parent
transition preserves strict order of both live intervals and the stronger
cross-boundary condition: every written parent is below every unread child's
parent. `level` and `all_levels` induct over successful node/level transitions;
`no_descending` rules out the prior (1,0) counterexample on ordered frontiers.
`MultiproofConeLiveLeaves.build_sorted` proves the deduplicating index fold on
a nondecreasing input, including ties; `batch_levels_sorted` composes that fold
with arbitrarily many levels. Rejection on duplicate digest disagreement is
outside the successful index fold and cannot create an accepted descending run.
These are mathematical index-carrier theorems, not a new whole source join.

The `cone4-order-1` host receipt verifies two exact-source per-step gates:
`live_order_step` checks the generated frozen binary_group's index write,
source/model pairing guard, mixed-prefix invariant and every cursor update;
`live_order_leaf` checks frozen leaf_insert's strict output and dedup branch.
Inputs, cursors, scratch suffix and observation coordinates are symbolic. The
hash in the index-only gate returns zero; no digest/log refinement is claimed
by that gate. No row or level is stubbed. All successful Lean declarations have
individual standard-axiom reports; the first failed elaboration is retained
and excluded. The manifest/receipts give all required metrics and source pins.

Still required: concrete extracted-array instantiation of the mathematical
index carrier, reached packed-key/index/opening provenance, physical window
adoption, and ordered model/log/batch simulation. The new induction does not
silently assert that the frozen production loop inhabits its Runs relation.
No complete multiproof AcceptedRunJoin or headline premise removal is claimed.

## Continuation 4, stage 2: physical `.get` and cursor rebase

`cone4-physical-1` verifies all three occupied/sibling/short physical node
roots: three completed solver results, exit 0, 127.791414 s, 990972 KiB peak
RSS, zero swaps. Scope: 6G/8G/no-swap/64 tasks; reservation and all immutable
source snapshots are retained. The gate compares the exact generated frozen
binary_group on arbitrary 5504-byte physical storage with that same body on
the borrowed 0..32-byte window, with relative cursor zero. It checks ordinary
short rejection, success, all scratch coordinates, i/w, exact cursor rebase,
call count and all hash-input bytes through arbitrary coordinate observations.
The sole verified stub is the unchanged hash observer; no reader/row/level is
stubbed. This closes the previously missing bounded P6 physical/window cut;
it does not claim a kernel-generated proof of Kani/library correspondence.

The retained kernel window/read32 lemmas and prior exact window-node gates
are reused unchanged. No full regression was repeated. Concrete extracted
live-array induction and ordered source/model log, leaf/count/padding/root
and two-batch composition remain open. No shipped file changed, so the frozen
ELF rebuild condition was not triggered; no byte-identity run is claimed.

## Continuation 4, stage 3: concrete extracted order induction

The mathematical carrier is now instantiated for the actual extracted arrays.
`MultiproofConeLiveReference.binary_shape` proves exact idx mutation and pair
consumption of `reference.binary_step`, without assuming sortedness or a source
equation. `MultiproofConeLivePreservation.binary_preserves`, `rows_sorted` and
`level_sorted` derive the mixed-prefix invariant for actual successful rows
and levels. `MultiproofConeLiveBatch.eighteen_sorted` inducts through the actual
extracted height loop; only HashTotal and initial domain/order remain. Neither
level preservation nor model RowJoin is assumed. `guard_eq` derives the
source-XOR/frozen-even-consecutive guard equation on each ordered unread suffix.

`MultiproofConeLiveBatch.leaf_projection` identifies the actual extracted
leaf insertion's index projection, including unequal-duplicate rejection.
`MultiproofConeLiveFold.fold_projection` / `fold_sorted` induct over structural
iteration of that actual step. `sorted_batch` composes the actual extracted
sort's proved order with this insertion fold. Its leaf/key projection remains
an explicit caller adapter, rather than an assumption that the output is
sorted. The initial scratch suffix is arbitrary and no distinct-query or
digest-consistency antecedent is added. The concrete frozen batch loop's
factoring and selected-opening/hash provenance remain P6/source obligations.

`cone4-keys-1` independently checks reached `batch_keys` for both batch sizes
and all three trees: exact index/relative-position projections, key bounds,
and monotonicity through the u64-shift/u32-cast. One completed solver result,
exit 0, 1.887354 s, 184428 KiB RSS, zero swaps, with the prescribed capped scope.
Existing sort and leaf-hash certificates are reused for unchanged bodies.

All successful new theorems have individual standard-axiom reports. Failed
local elaborations are retained but not accepted as evidence; no resource or
proof limit was raised. Receipts/manifest pin exact targets, source revisions,
hashes, dependencies, exits, time/RSS/swaps and every axiom report.
The stronger invariant removes the descending-pair obstruction for this
concrete extracted loop. It does not identify the source log with runLevel or
construct a complete multiproof ConeLogJoin/AcceptedRunJoin.

## Continuation 4, stage 4: ordered logical level comparison

`MultiproofConeOrderedLevel.level_program` proves exact Program identity
between a logical source-shaped level retaining the XOR guard and the frozen
`runLevel`, on every ascending live list and arbitrary supplied bytes/fuel.
`level_log` gives exact read/answer order for every oracle. Rejection on short
siblings is retained; no injectivity, collision-freedom, distinct addresses,
or accepted/honest-run premise is used. The proof inducts on fuel and applies
the already proved pairing equivalence, without unrolling a concrete tree.
Attempt 2: exit 0, 25.016042 s, 3587522560-byte RSS, zero swaps; both axiom
reports are standard. This is a logical level program theorem, explicitly
not a complete physical-array or batch source-log simulation.

### Precise remaining interface blocker

The current concrete extraction endpoint is
`reference.levels D hash scratch physical height : Result reference.Level`.
It exposes neither a Program nor a returned ordered log. The target slot
`verifySlot_frozen` is a `Program Bytes State Bool`, and `ConeLogJoin` quantifies
over that full Program observation through a concrete dependent Signature and
Implementation. `eighteen_sorted` and `eighteen_eq` therefore do not type as
that cone certificate; replacing the physical source with sourceLevel would
assume the missing representation/log theorem. The new `level_program` proves
only the final logical comparison, not the absent concrete identification.
This is an interface gap, not a counterexample to reached source correctness.

The next concrete deliverable is an instrumented physical node/level carrier
with a proved relation between (written parent prefix, unread child suffix,
physical cursor/remaining sibling bytes, digest arrays) and the Live argument
of sourceLevel, preserving each actual hash input before overwrite. It must
compose the checked one-call P6 observations into the returned ordered program,
then carry that relation through height 18. After that come exact key/opening,
leaf/count/padding/root adapters and both short-circuited three-slot batches
of dV_frozen2. Caller lowering remains excluded and assigned to S2.

No complete multiproof ConeLogJoin/AcceptedRunJoin is constructed and no
headline premise is removed. The CONE-AUDIT whole-cone classification remains
(d). The focused sorted-index and physical-rebase gates are closed at their
stated boundaries; the complete accepted-run target is not yet established.


## Continuation 4 final focused audit

`MultiproofConeLiveFreeze`, attempt 1, imports the new dependency closure plus
the unchanged frozen2 cone consumer: exit 0; wall 23.831808 s; peak RSS
3535912960 bytes; zero swaps; source revision
`6a4b840ee` (full revision/source SHA/direct-import fingerprint in receipt).
All twelve final reports are standard; every new theorem also has its own
report. This is focused compatible-cache compilation, not a coherent frozen
release manifest replay. The new audit verifies all eight current modules,
41 standard reports, six newly completed Kani roots, and the unchanged reused
hash/window certificates and callees. It records failed elaborations as
historical diagnostics, not accepted proofs. No unchanged full regression ran.

Reproduce the deterministic source/evidence audit with:

```sh
python3 -B tools/multiproof-cone-20261021/audit-live.py
```

`audit-live-result.json` records the result and the precise retained boundary;
its `complete_multiproof_source_cone` and `accepted_run_join_constructed` fields
remain false. Stage 1/2 local goals have new successful certificates and
concrete extracted order induction. Full reached-source adoption still needs
the caller/key/opening projection. Stage 3 is logical-level ordered Program
closure only; physical Live/log identification and stage 4's slot/batch join
remain blocked at the interface described above. No conclusion about a whole
source cone or security headline is inferred from these focused results.

Shipped crates, Session A candidates, sibling modules and inherited Lean files
are unchanged from this worktree's base. No frozen ELF rebuild was triggered
or byte-identity measurement claimed. No keys or wallets were touched; no push
or merge occurred. Source snapshots identify tested edits precisely even when
the receipt's checkout revision predates their reporting commit.

## Continuation 5, stage 1a: extracted digest writer provenance

Branch `codex/cx-multiproof-cone5-20261021`. New additive module
`MultiproofConePhysicalDigest.write_observed` proves that the actual extracted
parent writer requests exactly `[0x12], left, right`, receives the witnessed
digest from that very callback, and writes exactly that digest and index/2 at
w. `set_digest` proves every other digest coordinate is unchanged. No desired
Live relation, complete level equation, or successful-source hypothesis is
assumed; HashTotal and w<16 are retained. This is a local writer fact, not the
complete physical scratch-to-Live induction or a source log theorem.

Focused attempt 3: exit 0, wall 11.525027 s, peak RSS 3660513280 bytes,
zero swaps. All three individual axiom reports use only standard axioms.
Exact revision, source/dependency hashes, command and logs are recorded in
`MultiproofConePhysicalDigest-3/receipt.json` and `manifest.json`. Failed
elaborations 1/2 are diagnostics, not accepted proofs. The new compile5
launcher writes only into the continuation-5 private object directory and
reuses prior caches. No shipped crate or inherited Lean module changed.

## Continuation 5, stage 2a: exact packed key adapters

`MultiproofConeKeyAdapters.packed_index` and `packed_opening` prove both
projections of each reached u64 key: the high field is the query-derived tree
index, and the low-byte relative ordinal plus the batch start selects exactly
the original absolute opening. `sorted_stream` composes these with the actual
extracted sort and proves the whole sorted `(index,absolute opening)` stream,
including query ties and both batch sizes. Its only source-carrier premise is
the initial batch_keys prefix equation; that premise remains at the existing
independent P6 key-generator boundary. The raw proof opening/hash callback
adapter is not discharged by this index/ordinal theorem.

Focused attempt 2: exit 0, wall 15.901830 s, peak RSS 3579215872 bytes,
zero swaps. All five individual reports have standard axioms only; complete
revision/hash/dependency/command fields are retained in the module receipt and
manifest. Attempt 1 is an elaboration diagnostic. No shared objects or shipped
files changed, and no runtime or ELF regression was triggered.
