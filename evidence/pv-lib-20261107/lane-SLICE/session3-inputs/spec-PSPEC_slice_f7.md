# PSPEC slice:f7, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `core::ops::try_trait::impl[inherent]::wrap_mut_1::impl[7]::call_once`. Frozen syntax `lean/PV_STX2_SliceF7.lean` at `55002ec0e2eecdcafc22d27d8c97dde5954268c1` on `codex/pv-stx-20261104`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_slice_f7`: NeverShortCircuit wrapper capture and source index
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_slice_f7` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_slice_f7`: Invoke the inner generator and wrap its value in NeverShortCircuit, preserving its effects.

Use f8 provider definitions literally, including its capture-update and full explicit outcome store. After a successful call, the selected drop at source178 is the emitted f22 NeverShortCircuit closure destructor. Its no-foreign-store-write fact is proved by W2 TypedDestructor, not chosen as an identity delta.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_slice_f7` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 173 | `slice:f8` |
| 168 | `slice:builtin:Drop` |
| 178 | `slice:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The preliminary Statements.Pre fixes resolver clauses and omits the full typed generator/capture domain; Through8/OtherComposition and DropLive are named pending targets. W2 session10 adds TypedContract.Pre, actual typed f22 destruction and a conditional runtime contract, but f6SourceFrame.Contract, carrier/runtime binding and joint nonemptiness are still pending. New spec retains these as provider/caller discharge obligations, not proof assumptions hidden in Pre.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Drop the freshly returned Vec and then return its dangling descriptor.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
