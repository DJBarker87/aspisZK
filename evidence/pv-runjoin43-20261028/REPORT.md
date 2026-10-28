# Runjoin43 — active caller-domain composition

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch `codex/pv-runjoin-20261026`.
Entry `cbec9b692502c78e2d4914724f3c51c2408838e3`, resume LOG D401.
Assigned IDs 60400–60499; audit IDs 60497–60499. Budget 100 Lean attempts, 0 Kani.

**Work in progress. Target not yet established. Whole rows removed: 0.**

Current receipts: 22 launched single-module attempts, 12 accepted,
10 rejected. Reservation refusals are uncharged; same unlaunched IDs
are retained after the full cooldown. No cap increase, unchanged failed rerun,
Kani launch, native claim, or full regression has occurred.

## Checked results so far

RecordPost43 carries framing and exact output length through actual semantic_row.
ZeroShapes43 and RoundShapes43 identify every bounded source row counter by scalar
value laws. ZeroRows43 and ZeroComplete43 prove the actual successful zero-claim
owner appends 50 bytes and preserves its original prefix. RoundRecord43 proves
that an actual successful sumcheck round appends its five-byte header and 896-byte
canonical polynomial payload. RoundStream43 derives all canonical round offsets.
RecordSlice43, CanonicalRecord43 and ByteExtension43 preserve these payload slots
through later appends. CloneBytes43 proves the complete actual root byte copy.
PostMap43 transports source postconditions without changing any execution.

The actual caller composition, accumulator and layout-piece applications are
written and remain staged pending focused checks. No caller-domain obligation
is reported discharged until that composition compiles. Steps (2)–(4) remain
unstarted, preserving the requested order.

## Boundaries retained

No endpoint field or ledger row has been removed, added, weakened or changed.
All eight PV_RunJoin_Premises fields and the three TrustItems remain.
V038, V045, V163, V165, V167 and V244 remain open in their existing scope.
The op227 bridge stays a named hypothesis outside credited endpoint results.
No observer, simulator, failure/divergence, bad/query event, key, Rust source,
release artifact, other worktree or shared cache is changed.

## Evidence

The initial read-only preflight verifies 2633 source/object pairs, 5519 import
fingerprints, 5673 external objects and 5438 IR companions. New launches reuse
the pinned runjoin32-lean workspace under MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -M7000, one scope at a time.
`receipt-*.json` and `modules-*.json` retain exact targets, revisions/blobs/hashes,
dependencies, exits, wall times, RSS, swap and printed axioms. Accepted printed
axioms are standard only; rejected candidates retain their original Git blobs.

Next: finish CanonicalAppend43, RoundAccum43, RoundComplete43, LayoutPieces43,
then compile CallerDomain43 and CallerSuccess43 against those verified objects.

## Stage (1) completed

CallerDomain43.post (60430) and CallerSuccess43.success (60432) compile against
the actual build_with_helper_mode definition. Every successful emitted output
has length 13831 and satisfies SemanticDomain40.Domain. All 27 entries in
caller-domain-obligations.json are now discharged by the whole-caller theorem.
No successful encoder/loop or desired byte equality is an input premise;
no semantic-oracle meaning or op227 law is assumed. Source failure/divergence
observations retain their scope. The single-module caller scope used 9.36 s,
4519825408 peak RSS bytes and zero swap. Standard axioms only.

Stage (2) begins with the 39 historically staged opening prerequisites:
opening-prerequisite-preflight.json verifies their selected source hashes and
that no compiled object exists. opening-prerequisite-order.json gives the
exact topological order and assigned IDs 60433–60471. Previously accepted
source/object pairs are reused unchanged.
