# PSPEC slice:f21, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `alloc::slice::impl[inherent]::to_vec_in::impl[17]::to_vec`. Frozen syntax `lean/PV_STX2_SliceF21.lean` at `55002ec0e2eecdcafc22d27d8c97dde5954268c1` on `codex/pv-stx-20261104`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_slice_f21`: Source pointer, public length n, allocator; readable registered M31 range, OwnerWellFormed, typed length/layout constraints
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_slice_f21` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_slice_f21`: Return a fresh owned Vec of length n containing the entry source bytes. Include zero length, allocation/layout error and null branches. Execute copy and set_len, and return to the saved f13 caller with the explicit final store.

Use PV_STX2_ToVecCallReferenceEntry.Pre and its reference-valid OWNER definitions by name. Positive n allocates the actual M31 layout, copies exactly 4*n pre-state bytes into a fresh disjoint destination, performs set_len and returns the source Vec representation. For n=0 return the aligned non-null dangling zero-capacity Vec with no malloc/copy. Signed-size rejection, null allocation, resource failure/divergence/pending and copy exceptions retain their exact branches. Fix Pending to require completed=none and programs(callee)=none.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_slice_f21` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 581 | `slice:f31` |
| 624 | `slice:f32` |
| 653 | `slice:f33` |
| 630 | `slice:builtin:CopyNonOverlapping` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

ToVecCallSpecification already states MachineSpec, reference validity, numbered entry and positive ownership. Pending omits completed=none and native-dispatch resolver test (session88 actual_entry_false_pending). Post existential finite fuel alone has no separate infinite-divergence alternative; undefined is excluded without an adequate source binding. It constrains internal state after abort; new observable abort carries events only. New spec preserves zero/positive/error branches and requires first ACTUAL boundary.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

On an empty slice, claim pending at prefix11 merely because the ignored fallback handler says pending: prefix11 is an f31 BODY push with no native answer consumed.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
