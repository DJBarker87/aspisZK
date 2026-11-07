# PSPEC thread:f220, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `core::panic::unwind_safe::impl[26]::call_once`. Frozen syntax `lean/PV_THR2_F220.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f220`: AssertUnwindSafe wrapper and callback arguments
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f220` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f220`: Unwrap the actual wrapper and invoke f208 at the source arguments; return its reply and effects.

Unwrap AssertUnwindSafe using its source aggregate, then invoke f208 with the same argument tuple; preserve callback effects and its exact nested Result.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f220` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 9244 | `thread:f208` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Wrap a constant result without running the enclosed closure.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
