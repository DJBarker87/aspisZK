# PSPEC thread:f0, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `aspis_r1_cert_check::native_workers::ordered_families`. Frozen syntax `lean/PV_THR2_F0.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f0`: n, worker function/captures; OrderedFamiliesEntryOwned' with registry/representation linkage
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f0` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f0`: Return the ordered family Vec on completion, preserving captures; all scope, worker, allocation and OS resource outcomes remain observable in source order.

Entry is OrderedFamiliesEntryOwned' for the ACTUAL captures, including linked source address, typed validity, registry and numbering. Retain the full ordered result and all allocation, scope and OS effects on every source branch.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f0` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 16 | `thread:f1` |
| 8 | `thread:builtin:Drop` |
| 12 | `thread:builtin:Drop` |
| 22 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Return an empty family for n=1 and a worker producing a nonempty result.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
