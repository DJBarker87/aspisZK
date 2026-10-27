# L188 Debug formatter preparation handoff

Branch `codex/cx-debug-fmt-20261026`. Evidence-only candidate; NOT applied to
research or any generated source owner. No push. Target not yet established.

## Exact result and limits

DFm_remove-debug.patch removes two contiguous derive(Debug) declaration blocks
(50 lines each) from the exact selected parser source variants. Review the
candidate copies in DFm_regenerated, and reproduce with DFm_prepare.py --check.
`git apply --check --unidiff-zero` passes. The patch is intentionally unapplied.
These are source-filtered copies, not a fresh Rust/Charon/Aeneas extraction.

Both modified Funs modules and ALL SIX direct importers compile. Five additional
transitive consumers compile (11 importer modules total; exact list in
DFm_importers-split.json). All 212 retained generated declarations and all 268
inspected importer declarations have the same complete expression graphs modulo
bound-variable names and explicitly compared compiler-helper renamings. Parser
comparison uses full Expr representations; importer comparison preserves sharing
and hashes complete canonical DAG nodes. This is checked structural evidence,
not a new Lean equivalence theorem or literal object-byte identity.

The strongest literal claim is false: deletion renames seven parser matchers,
including two axiom-free matchers shared with Error equality, plus sixteen
private splitter/equation/simp helpers in importers. Initial comparison reports
are retained; refined reports compare every renamed helper's type and body too.
Three public theorem proof terms change only by those helper names; their types
are unchanged. No public computational definition changes in the inspected set.
The earlier commentary's "ownership" description was imprecise: the additional
differences are generated helper NAMES, recorded in DFm_importer-renamings.json.

DFm_source-reference-audit.json checks all 1,489 hash-matched selected sources:
only the two generated Funs files mention formatter symbols explicitly. This
lexical audit is not a replay of 1,487 transitive importers. The remaining 1,476
were NOT rebuilt here. All other dependencies use the coherent SInt2 cached
workspace. RPz3 owns actual-top formatter reachability; it was not duplicated.

## Exact declarations and axiom provenance

For EACH namespace N = AspisR1RecordParser, AspisR1PrefixAggregateParser:

- N.r1_wire.Error.Insts.CoreFmtDebug.fmt
- N.r1_wire.Error.Insts.CoreFmtDebug
- fmt._proof_1 through fmt._proof_16 (generated proof helpers)
- fmt._native.decide.ax_1 through fmt._native.decide.ax_18 (generated axioms)

Together these are 72 exclusively-Debug declarations. The shared
fmt.match_1 is NOT exclusive: Error equality uses it. Re-elaboration regenerates
identical matcher functionality as CoreCmpPartialEqError.eq.match_1. Its removal
is not mistaken for removal of an unused logical dependency.

The 37 nonstandard names are the two sets of 18 native axiom names above plus
Aeneas.Std.core.fmt.Formatter. DFm_removed-declarations.json lists every exact
name and matcher replacement. The library Formatter axiom remains in the import
environment; none of the retained parser/importer declarations depends on it.
The 480 after-context #print axioms queries use only subsets of propext,
Classical.choice and Quot.sound. No new top theorem or security axiom was added.

The actual Rust roots are header-array F and prefix-E-exact, with Error deriving
Debug at source/lib.rs:131. Generated comments link the fmt and trait record to
that derive. Aeneas core fmt supplies the placeholder; toStr's native default
proof supplies each formatter's 18 string-bound axioms. The evidence does not
claim there is a separately imported parser FunsExternal file: there is none.
Full paths, hashes and extraction commands are in the provenance JSON files.

DFm_EXTRACTION-PROPOSAL.md proposes excluding core::fmt::Debug and its impls at
the Charon extraction boundary; syntax is supported by pinned-source inspection,
but actual extraction behavior (including its documented trait-impl limitation)
needs testing. No Rust derive, extraction config, generated research file or
library axiom is edited. Do not adopt an opaque fmt replacement.

## Budget, failures, resource receipts

Budget exhausted: 40/40 Lean, 0/0 Kani. 37 passed, 3 failed. Thirteen source
module builds passed (2 parsers + 11 importers); 24 inspection modules passed.
DFm_compile-summary.json contains exact targets/argv source revision/hash,
direct object pins, exit, wall, RSS, swaps, cgroup limits and full axiom output.
Compiler wall sum 85.512240444 s; peak RSS 7,386,260 KiB; swaps zero. Successful
after-context audits cover 480 declarations; 1,070 total raw print results also
include baseline inspections and the unchanged sources' own print commands.
All scopes: MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, -j1 -M7000.

Failures: DFm_001 namespace-overlay Types object selection (fixed by pinned
unchanged artifact links); DFm_004 missing Repr instance in inspection code
(replaced by explicit constructor encoding); DFm_007 excessive memory at fixed
-M7000 during expanded expression rendering (exit134, 20.630495230 s). The last
was replaced by single-module shared-expression graphs, NOT retried unchanged.
No cap increase, timeout, Rust/Kani/SBF build or package/manifest replay occurred.

Infrastructure defect discovered AFTER the last compile: S2H_reservation.py's
quiet-window branch writes allowed=false but exits ZERO. The inherited exit-code
caller therefore invoked systemd-run for DFm_007; the shared shim correctly
waited outside any scope until the marker was withdrawn. However, there is no
valid aggregate-reservation receipt for that FAILED inspection. All 37 passing
attempts have allowed=true receipts. No admission guarantee for attempt7 is
invented. No infrastructure was repaired. The lead should fix the barrier's
quiet exit status and require JSON allowed=true, then re-admit after any shim
wait. The historical orchestration is disabled at its exhausted 40-attempt
budget; no further build is authorized. DFm_ADMISSION-DEFECT.md has exact detail.

Final process inspection found zero own compilers/runners. Host objects and raw
expression snapshots stay on host; only their hashes/sizes and comparisons are
committed. DFm_object-inventory.json pins the isolated overlay. No binaries,
oleans, archives, keys or ELFs are committed or destroyed.

## Actual top, ledger, non-vacuity and next gate

Latest committed actual top is AspisR1.Rc8_Top.deployed. DFm_before-after.md
contains its complete identical statement. Premises removed/added/changed:
0/0/0. DFm_ledger-delta.json mechanically recounts the unchanged inherited rows:
raw actual83T/19P/13G; distinct83T/18P/13G; combined nonalias raw89T/23P/13G,
distinct89T/22P/13G. All C0; delta T0/P0/G0/C0. Aliases L137/L134 and
L185/L159 are retained. No quantifier, carrier, event, conclusion, metric,
trust item or runtime admission changes. This preparation earns no closure row.

Non-vacuity remains inherited and conditional: Rc8_Nonvacuity.composed and
Rc8_Clean.exists_world retain their hypotheses. No joint premise inhabitant is
constructed; JFt_ owns the joint real-byte fixture. Passing imports do not
establish that result. No actual top #print axioms/release closure is claimed.

Next deliverable: lead review/adoption of extraction filtering, successful
re-extraction with retained expression comparison, remaining importer/full
coherent release replay and RPz3's actual-top/trust audit. L188 stays OPEN.
No shipped source changed, so no ELF rebuild trigger. Historical pins retained,
not freshly reproduced: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
