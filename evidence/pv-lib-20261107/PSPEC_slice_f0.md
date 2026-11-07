# PSPEC slice:f0, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `aspis_statement::state_only_trace::impl[0]::clone`. Frozen syntax `lean/PV_STX2_SliceF0.lean` at `55002ec0e2eecdcafc22d27d8c97dde5954268c1` on `codex/pv-stx-20261104`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_slice_f0`: Foundation reference; Source7EntryOwned''' including registry linkage and OwnerWellFormed
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_slice_f0` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_slice_f0`: Return the cloned Foundation: sixteen owned columns, each with the entry column length and bytes, with disjoint fresh destination regions and entry regions preserved.

Each of the sixteen output columns has a distinct fresh OWNER identity and byte-for-byte equality with the corresponding ENTRY column; source and earlier columns survive later allocation/copy. The Foundation wrapper is rebuilt using its emitted aggregate kind. The Foundation construction caller discharges Source7EntryOwned with registry linkage, OWNER invariants and full typed reference validity.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_slice_f0` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 8 | `slice:f1` |
| 13 | `slice:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Return the original Foundation by shallow copying its sixteen Vec descriptors. Positive-length source column 0 then shares its allocation with the result, violating freshness.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
