# PLIB session 2 — partial library, no row consumption

Branch `codex/pv-lib-20261107`; session 2 starts at `3e84e9ed97d`.
Owner-authorized D974/D975 preparation only. No push/merge or package-branch,
ledger, checker, pv-common, implementation or key changes. Endpoint premises
removed 0, added 0; no trust/metric change. Target not yet established.

All evidence paths below are under `evidence/pv-lib-20261107/`.

## Exact progress and limits

The 29 normative Markdown specs remain byte-for-byte frozen under FREEZE.json.
They are NOT 29 compiled Lean contracts. No SPEC_CORRECTIONS was needed.
PLIB_MAP.json/.md now covers 170 slots: **110 INSTANTIATED, 55
MISSING-CHILD-LEMMA, 5 SPEC-ERROR**, versus 19/146/5 at session 2 entry.
INSTANCES.json names 83 compiled, raw-audited provider fields (67 new).
An instantiated slot means a qualified provider-model graph adapter; actual
caller/domain/handler transport remains where its qualification says so.
No parent row or whole-root composition was closed.

Session 2 adds deterministic Drop/Box/Atomic121/Arc124/count/ArcClone360,
named thread/native full-reply, slice allocation/constructor/copy/native/
builtin/ptr graph groups. Each reuses provider definitions and existing named
semantics by name. No new documented-semantics fact was introduced. Native
models retain arbitrary full replies and the CLOSED root's explicit reachable
effects; they do not supply missing actual source-store writes or stronger
value/frame claims. SESSION2_FIELDS.json is the exact field manifest.

There were 119 passing focused session-2 compiles: 85 byte-identical pinned
provider replays, 33 new library/support modules, and the new-root audit driver.
Every passing compile has its own commit and receipt. The pinned D937 cache
was reused; only missing dependent providers were replayed, one focused target
at a time. VALIDATION.json checks every replay against its pinned git source
and every active library source against an accepted receipt.

PV_LIB_Registry.certified proves the concrete native lift graph and places/next
frame on every answer; abort exposes events only. This does NOT prove its
binding to actual OwnInit or composition with explicit OWNER actions, so the
registryFrame facet remains MISSING. Arc count and clone certificates similarly
do not silently close their actual-caller facets.

## Compiled comparison and outstanding deliverable

PV_LIB_SourceStoreComparison compiled49456. cell_gap compares the original
f289 native delivery with the existing exact CellReplace289 source meaning;
public_gap shows the changed cell distinguishes the public observations on a
returning reply. Reference/destination separation is explicit. This is a
component comparison, NOT actual f170 setter-path provenance, NOT a full frozen
Pre-to-package-contract implication. SESSION2_COMPARISON.md records the scope.
The requested compiled comparison of all 29 frozen contracts remains unfinished.
The prior prose comparisons remain normative analysis only.

## Strict audit — complete, do not rerun unchanged

Baseline49480 (38 roots) was reused, never rerun. ONE session-2 strict audit
**49481 passed 82/82 new roots**, zero unresolved, zero raw/summary mismatch,
only propext/Classical.choice/Quot.sound. Exit0; wall0:10.05;
peak7002692KiB; swaps0; source revision63a5c15a7a81ac57e2cacd6b21acb41c67598af4.
SESSION2_RAW_AUDIT.json, SESSION2_RAW_GRAPH_MANIFEST.json and compressed graph
archive retain the results. The private importAll walker and collector body
are unchanged; only module/root input lists changed. Provenance is recorded.
#print axioms summaries alone are not called raw audits.

Six session-2 elaboration failures were repaired with changed source, archived
and never loaded as accepted evidence. Six admission refusals spent IDs and
received at least180s cooldown.49452 failed source/object-authority preflight
before Lean: a source file in the cache was not an accepted object. The two W4
providers were then replayed unchanged49453/49454. No OOM, cap increase, heavy
local build, extraction, Kani or complete-manifest replay occurred.

## Concrete next work

REMAINING.md enumerates all gaps. Eleven distinct CLOSED providers still lack
adapters: slice32/33; thread9/10/93/167; thread277/278/279/280/612. In addition,
30 edges have OPEN/PARTIAL suppliers, nine facets remain unbound and five
SPEC-ERROR facets remain. OwnInit's dependency chain and slice root remain
uncomposed. The syntactic DAG is acyclic; joint premise nonemptiness and actual
source/machine adequacy are not proved. Existing obstructions are retained in
TOP_COMPOSITION.md; the component comparison does not close them.

Next unused Lean ID49458 (authorized through49479). ID49452 is spent.
Next raw ID49482 is available only for genuinely changed/new roots in further
work; never rerun49481 unchanged. Unused IDs are not a claim of exhaustion.
Host writes remain ONLY /home/dombarker/project-offloads/codex-pv-lib-20261107.
One scope at a time:6G/8G/swap0/Tasks64/Lean-M7000, fresh standalone
STREAMB_SLOTS=1 turn.sh before each ID. No row proofs consume this library.
