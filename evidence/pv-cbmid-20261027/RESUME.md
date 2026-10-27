# Active work state (not a completion report)

Branch codex/pv-cbmid-20261027; base237e135561; latest source stage7724872f2e.
Rows0→0; endpoint premises unchanged; target not yet established.
TALLY.json is authoritative. IDs40600-40899, never reuse; reserve charged98-100 for audits.
Lean21/100 and Kani3/10 at this checkpoint. No local Lean and no subagents.
Only own PV_CBM modules go into shared sources. ProverRw* remain read-only.
Host setup reuses exact-hash cb3 source (no sibling writes); cb3/lean-objects absent.

Checked: InventoryShape, PathGeometry/Classification, ValueClassification,
Padding/Path/Value bijections, InventoryCardinality.cardinal=3803,
CellEnumeration, PushList generic append lemma, ReferenceTypes,
MasksReference/Selection, CallbackBundle.op134_reference. All latest passed
axioms standard. Earlier failed attempts and error-recovery sorryAx diagnostics
are retained as failures, never accepted as proofs.

Kani: classifier source-prefix vs owned predicate PASS0/61, unwind25;
complete masks180s TIMEOUT; ruling(i) allows one retry, masks900s TIMEOUT.
Never a third identical mask gate. Same caps6G/8G/swap0/Tasks64/CPU0-3.
Kani RSS failures: GNU time parent maximum is incomplete; physical snapshot
near deadline retained separately, CBMC VmHWM6699344KiB, scope peak6873858048B.
No ROW counterexample. Reference equations are not opN_source laws.

Pending next: admission cooldown from admission-state.json (180s after refusal),
then run.py charon charon-op132ref-001 132ref (previous refusals uncharged;
no actual target.json exists yet), then aeneas aeneas-op132ref-001 132ref.
Owned reference has3803 literals in60 chunks of≤64 pushes, separately-owned
functions with no iterator/deref interface. prepare_cells.py consumes its
actual Aeneas output, emits exact chunks plus named PushList proof and free-cell
classification applications; --check must pass. Compile generic ValueFree and
CellTypes, then one chunk first, then remaining distinct chunks once, then bridge.
All scopes strictly serial, one per job.

Also prepared indexed op79 reference preserving basis operation order. Need
setup uploaded reference_encoder.rs at setup-encoder-002 (done), then extract
79ref and133ref. Source op132/133/79 direct Aeneas graphs failed explicit
escaping-reference/structured-Drop preflight. Optional222/224 exact source
fragments pinned in FRAGMENT-PINS.json; fresh sibling check before those ops.
No sibling op132/133/134/79/222/224_source found at latest checked branch heads
95a7a8e2e1, e73d646b9b, 1b71b2650f.

Further Kani candidates already in source-lib.rs: checks::rows_complete(unwind257),
schedule_checks::schedule_success(unwind137), encoder_checks::eval_qm31_complete
(unwind1025, fully arbitrary canonical1024 QM31 coefficients andpoint). Complete
cells harness still to add. P6 op79 also needs WideExact and actual caller
canonicality; base-field-only gates would not suffice.

Use whole budget, no early stop on Aeneas/Kani failure. Source/receipt commits
path-limited; no push/merge or crates/programs edits. Before final audit commit
source; last3charged targets distinct focused reference audit, inventory audit,
one final bundle/manifest audit. No unchanged full regression.
