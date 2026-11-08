# PSPEC thread:f15, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `aspis_r1_cert_check::native_workers::ordered_map_inner::impl[3]::call_once`. Frozen syntax `lean/PV_THR2_F15.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f15`: Actual scope reference and captured n/f, with entry-owned capture registration
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f15` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f15`: Construct handles, iterate next93, spawn f166 on each Some index with source-derived captures, push handles and join in source order; None exits without a ThreadInit allocation, preserving failures and explicit stores.

On next93 Some i execute exactly the source spawn of i with actual n/f/scope capture and then push its handle; None exits without allocating a ThreadInit for that iteration. Joins and result order are preserved. The range start and handle Vec header writes are actual source-store actions, not backend-only changes.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f15` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 3398 | `thread:f164` |
| 3420 | `thread:f165` |
| 3447 | `thread:f93` |
| 3490 | `thread:f166` |
| 3519 | `thread:f167` |
| 3561 | `thread:f14` |
| 3591 | `thread:f7` |
| 3641 | `thread:f167` |
| 3693 | `thread:f8` |
| 3756 | `thread:f9` |
| 3859 | `thread:f168` |
| 4327 | `thread:f167` |
| 3411 | `thread:builtin:Drop` |
| 3438 | `thread:builtin:Drop` |
| 3481 | `thread:builtin:Drop` |
| 3501 | `thread:builtin:Drop` |
| 3510 | `thread:builtin:Drop` |
| 3552 | `thread:builtin:Drop` |
| 3573 | `thread:builtin:Drop` |
| 3582 | `thread:builtin:Drop` |
| 3605 | `thread:builtin:Drop` |
| 3614 | `thread:builtin:Drop` |
| 3623 | `thread:builtin:Drop` |
| 3632 | `thread:builtin:Drop` |
| 3657 | `thread:builtin:Drop` |
| 3666 | `thread:builtin:Drop` |
| 3675 | `thread:builtin:Drop` |
| 3684 | `thread:builtin:Drop` |
| 3711 | `thread:builtin:Drop` |
| 3720 | `thread:builtin:Drop` |
| 3729 | `thread:builtin:Drop` |
| 3738 | `thread:builtin:Drop` |
| 3747 | `thread:builtin:Drop` |
| 3787 | `thread:builtin:Drop` |
| 3796 | `thread:builtin:Drop` |
| 3805 | `thread:builtin:Drop` |
| 3814 | `thread:builtin:Drop` |
| 3823 | `thread:builtin:Drop` |
| 3832 | `thread:builtin:Drop` |
| 3841 | `thread:builtin:Drop` |
| 3850 | `thread:builtin:Drop` |
| 3945 | `thread:builtin:Drop` |
| 3873 | `thread:builtin:Drop` |
| 3882 | `thread:builtin:Drop` |
| 3891 | `thread:builtin:Drop` |
| 3900 | `thread:builtin:Drop` |
| 3909 | `thread:builtin:Drop` |
| 3918 | `thread:builtin:Drop` |
| 3927 | `thread:builtin:Drop` |
| 3936 | `thread:builtin:Drop` |
| 4052 | `thread:builtin:Drop` |
| 3962 | `thread:builtin:Drop` |
| 3971 | `thread:builtin:Drop` |
| 3980 | `thread:builtin:Drop` |
| 3989 | `thread:builtin:Drop` |
| 3998 | `thread:builtin:Drop` |
| 4007 | `thread:builtin:Drop` |
| 4016 | `thread:builtin:Drop` |
| 4025 | `thread:builtin:Drop` |
| 4034 | `thread:builtin:Drop` |
| 4043 | `thread:builtin:Drop` |
| 4144 | `thread:builtin:Drop` |
| 4063 | `thread:builtin:Drop` |
| 4072 | `thread:builtin:Drop` |
| 4081 | `thread:builtin:Drop` |
| 4090 | `thread:builtin:Drop` |
| 4099 | `thread:builtin:Drop` |
| 4108 | `thread:builtin:Drop` |
| 4117 | `thread:builtin:Drop` |
| 4126 | `thread:builtin:Drop` |
| 4135 | `thread:builtin:Drop` |
| 4226 | `thread:builtin:Drop` |
| 4154 | `thread:builtin:Drop` |
| 4163 | `thread:builtin:Drop` |
| 4172 | `thread:builtin:Drop` |
| 4181 | `thread:builtin:Drop` |
| 4190 | `thread:builtin:Drop` |
| 4199 | `thread:builtin:Drop` |
| 4208 | `thread:builtin:Drop` |
| 4217 | `thread:builtin:Drop` |
| 4246 | `thread:builtin:Drop` |
| 4255 | `thread:builtin:Drop` |
| 4264 | `thread:builtin:Drop` |
| 4273 | `thread:builtin:Drop` |
| 4282 | `thread:builtin:Drop` |
| 4291 | `thread:builtin:Drop` |
| 4300 | `thread:builtin:Drop` |
| 4309 | `thread:builtin:Drop` |
| 4318 | `thread:builtin:Drop` |
| 4401 | `thread:builtin:Drop` |
| 4338 | `thread:builtin:Drop` |
| 4347 | `thread:builtin:Drop` |
| 4356 | `thread:builtin:Drop` |
| 4365 | `thread:builtin:Drop` |
| 4374 | `thread:builtin:Drop` |
| 4383 | `thread:builtin:Drop` |
| 4392 | `thread:builtin:Drop` |
| 4467 | `thread:builtin:Drop` |
| 4413 | `thread:builtin:Drop` |
| 4422 | `thread:builtin:Drop` |
| 4431 | `thread:builtin:Drop` |
| 4440 | `thread:builtin:Drop` |
| 4449 | `thread:builtin:Drop` |
| 4458 | `thread:builtin:Drop` |
| 4522 | `thread:builtin:Drop` |
| 4477 | `thread:builtin:Drop` |
| 4486 | `thread:builtin:Drop` |
| 4495 | `thread:builtin:Drop` |
| 4504 | `thread:builtin:Drop` |
| 4513 | `thread:builtin:Drop` |
| 4583 | `thread:builtin:Drop` |
| 4538 | `thread:builtin:Drop` |
| 4547 | `thread:builtin:Drop` |
| 4556 | `thread:builtin:Drop` |
| 4565 | `thread:builtin:Drop` |
| 4574 | `thread:builtin:Drop` |
| 4631 | `thread:builtin:Drop` |
| 4595 | `thread:builtin:Drop` |
| 4604 | `thread:builtin:Drop` |
| 4613 | `thread:builtin:Drop` |
| 4622 | `thread:builtin:Drop` |
| 4668 | `thread:builtin:Drop` |
| 4641 | `thread:builtin:Drop` |
| 4650 | `thread:builtin:Drop` |
| 4659 | `thread:builtin:Drop` |
| 4698 | `thread:builtin:Drop` |
| 4680 | `thread:builtin:Drop` |
| 4689 | `thread:builtin:Drop` |
| 4717 | `thread:builtin:Drop` |
| 4708 | `thread:builtin:Drop` |
| 4727 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The ledger PARTIAL evidence is a prefix/conditional contract, not this full own-entry all-outcome specification. The common machine/entry/frame/boundary clauses add thread22/23'/25/26/27 explicitly. Retain the provider representation by name; a new consumer representation is forbidden. No implication from the partial evidence to this specification is claimed.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Treat a next93 None as Some 0 and allocate/spawn a worker.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
