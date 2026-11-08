# PSPEC thread:f2, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `aspis_r1_cert_check::native_workers::is_worker`. Frozen syntax `lean/PV_THR2_F2.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f2`: Source TLS key and capture environment
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f2` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f2`: Return the actual worker flag read via the source TLS with callback; retain each TLS failure and preserve unrelated cells.

The getter callback is the source token and uses CLOSED18 at the actual TLS reference; its returned boolean is the stored Cell boolean. TLS initialization/access failure is retained.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f2` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 1706 | `thread:f17` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

W4 Statement/OriginalStatement modules describe conditional summary/caller composition. Their dependencies are still PARTIAL and their actual source-store-machine transport is unfinished. This spec uses the actual enlarged interpreter, thread25 and exact provider constructors; no conditional summary is treated as proof of the row.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Always return false when the actual initialized TLS Cell is true.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
