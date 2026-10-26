# EJR stage 4: bounded object recovery

Stage 4 stopped at its reserved limit: **799 Lean attempts** (30000–30798),
**766 passing validation**, **33 failed attempts**, plus **33 object reuses**
with matching module, source hash and selected dependency object hashes.
One attempt remains reserved for the stage-5 launcher smoke test. No Kani,
Rust, SBF or full frozen-manifest replay ran. No shipped source changed.

The counter includes the three library attempts: 30479 failed because a
required runtime IR companion was absent; 30480/30481 rebuilt the exact
archive-pinned Fmt/ArraySlice sources after restoring that companion from its
committed hash pin. The new object hashes differ from historical binaries.
234 other library modules and their pinned companions were reused byte-for-byte.
This is not a claim of a coherent frozen release rebuild or a full library
axioms audit.

All Lean runs used one module per scope, -M7000, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Admission receipts precede launches.
Peak recorded RSS: 7,168,572 KiB; all recorded process swaps: zero. Exact
commands, source revisions/hashes, selected dependencies/fingerprints, GNU
wall/RSS/swap/status and full printed axioms/errors are in receipts/.
`lean_exit` is the actual compiler status; `validation_exit`/`exit` also reject
printed sorryAx. No failed object is accepted as a dependency. Compiler error
placeholders are retained in logs, not credited as proved axioms.

## Infrastructure corrections and retained failures

Lean binds whole namespaces to selected roots; dangling earlier aliases can
shadow valid later files. The repaired roots bind complete intact core/package
namespaces inside the two authorized output directories. Surviving caches,
J.json and their source files were not modified. Generated library views were
snapshotted before directory bindings. Project fallback views use symlinks;
existing compiled regular objects are protected. Dependency ordering requires
selected producers in the same workspace to pass first. Identical project
objects are reused only after source and dependency hashes match.

The runner fingerprints the physical namespace/library/IR context as well as
direct dependency objects. Earlier import failures are distinct from the
repaired environment. The duplicate guard refused one old direct-only
fingerprint before Lean launched; no compile was charged for that refusal.

The coordinator was stopped once after child 30478 completed; its receipt was
recovered from its command, unchanged dependency fingerprint, output and GNU
time. The Lean child was not killed or rerun. Subsequent namespace mismatches
fail closed after a recorded attempt.

Actual proof/source blockers include:
- 30431, R1Z/SimCostOuterRetry6: omega/type errors.
- 30485, R1Z/EventsR1P2.card_NZ (line 16): kernel memory limit. Its shape is the
  nonzero-answer subtype cardinality via card_subtype_compl/card_ans; a symbolic
  instance-preserving cardinality proof must replace pathological reduction
  before any retry. This source was not rerun and the cap was not raised.
- 30589, R1Z/CertOwnFill: own_c1/own_val/own_col_loop/fill_own_loop API mismatch
  against the selected extracted provider; reconcile compatible receipt-pinned
  source variants before attempting a replacement.
- Historical metadata scans need their auxiliary scan inputs/environment;
  they are not ordinary proof-module compiles.

Other retained failed attempts are documented individually; many earlier import
failures subsequently passed in the repaired context. Source snapshots were
not silently edited to repair a theorem. The exact remaining queue and latest
failed keys are the handoff's resume plan, not a passing release manifest.

## Security accounting

AspisR1.Rc2_Top.deployed and every repository Lean source it imports are
unchanged. Before/after statement bytes and the Ledger_003–005/Cons/Rc2 recount
are supplied separately: zero T/P/C delta, no premise removed, added or changed.
Security non-vacuity is not newly established by cache recovery. S2 remains
OPEN; target not yet established. The stage-5 smoke theorem tests infrastructure
on inhabited Nat and is not a security conclusion.
