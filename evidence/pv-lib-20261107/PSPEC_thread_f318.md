# PSPEC thread:f318, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `core::intrinsics::catch_unwind`. Frozen syntax `None` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f318`: Actual catch_unwind callback pointers, data pointer and result storage, with valid source-typed captures.
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f318` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f318`: Execute the callback intrinsic and preserve its source success code, output cell, abort and stopped branches.

This is a HIGHER-ORDER intrinsic, not an arbitrary-result leaf. Call f316 once with the data pointer. On normal return use the intrinsic success code and actual output cell. Under pinned panic=abort, callback panic terminates and no unwind handler returns normally. Pending/failure/divergence stays at the actual callback site.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f318` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| documented-dispatch | `thread:f316` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Return the intrinsic success code without calling f316 or writing its result cell.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
