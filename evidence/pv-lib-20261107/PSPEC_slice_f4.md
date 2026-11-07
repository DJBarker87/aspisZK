# PSPEC slice:f4, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `core::array::try_from_fn`. Frozen syntax `lean/PV_STX2_SliceF4.lean` at `55002ec0e2eecdcafc22d27d8c97dde5954268c1` on `codex/pv-stx-20261104`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_slice_f4`: Generator and output element layout; public array length sixteen
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_slice_f4` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_slice_f4`: Return the complete initialized array if all generator calls continue; otherwise retain the first residual, its initialized prefix and the source cleanup effects.

ArrayRepeat creates sixteen uninitialized UNION carriers, not initialized Vec values. On Continue initialize the corresponding slot exactly once. Never read an uninitialized slot. On Break preserve the residual and cleanup only the initialized prefix. The f11 uninhabited residual conversion abort is retained if that emitted branch is reached.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_slice_f4` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 51 | `slice:f23` |
| 57 | `slice:builtin:"ArrayRepeat"` |
| 62 | `slice:builtin:"ArrayToSliceMut"` |
| 67 | `slice:f9` |
| 77 | `slice:f11` |
| 98 | `slice:f10` |
| 105 | `slice:f12` |
| documented-dispatch | `slice:f7` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Report a complete array after initializing only slot 0.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
