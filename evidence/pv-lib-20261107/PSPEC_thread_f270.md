# PSPEC thread:f270, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `std::thread::scoped::impl[inherent]::spawn_scoped`. Frozen syntax `lean/PV_THR2_F270.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f270`: Builder, scope reference and closure captures
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f270` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f270`: Clone scope bookkeeping and invoke spawn_unchecked with the actual closure and scope; return the actual scoped handle/Result with exact OS resource branches.

Use Builder.name and stack_size, clone the actual Scope Arc with nonzero strong count derived from construction, and pass the moved worker closure to f361. On source Err retain the exact error and earlier callback/Thread/Box allocations, not a post-success-only allocation arm.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f270` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 10098 | `thread:f360` |
| 10166 | `thread:f361` |
| 10197 | `thread:f279` |
| 10233 | `thread:f280` |
| 10048 | `thread:builtin:Drop` |
| 10059 | `thread:builtin:Drop` |
| 10083 | `thread:builtin:Drop` |
| 10116 | `thread:builtin:Drop` |
| 10127 | `thread:builtin:Drop` |
| 10151 | `thread:builtin:Drop` |
| 10183 | `thread:builtin:Drop` |
| 10219 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The ledger PARTIAL evidence is a prefix/conditional contract, not this full own-entry all-outcome specification. The common machine/entry/frame/boundary clauses add thread22/23'/25/26/27 explicitly. Retain the provider representation by name; a new consumer representation is forbidden. No implication from the partial evidence to this specification is claimed.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

On an OS spawn error, erase the preceding callback and ThreadInit allocation events.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
