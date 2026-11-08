# PSPEC thread:f166, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `std::thread::scoped::impl[inherent]::spawn`. Frozen syntax `lean/PV_THR2_F166.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f166`: Scope reference and actual move closure with registered captures
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f166` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f166`: Construct Builder, invoke spawn_scoped and consume its Result; on success return ScopedJoinHandle with the actual captures, preserving exact OS/failure effects.

Builder fields are source literals. f270 receives actual scope and moved closure. On Ok return its scoped handle; on Err the source expect child takes its panic/abort path including any formatting allocation before diagnostic effects.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f166` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 7916 | `thread:f269` |
| 7934 | `thread:f270` |
| 7954 | `thread:f271` |
| 7908 | `thread:builtin:Drop` |
| 7926 | `thread:builtin:Drop` |
| 7946 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The ledger PARTIAL evidence is a prefix/conditional contract, not this full own-entry all-outcome specification. The common machine/entry/frame/boundary clauses add thread22/23'/25/26/27 explicitly. Retain the provider representation by name; a new consumer representation is forbidden. No implication from the partial evidence to this specification is claimed.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Convert spawn Err into an arbitrary success handle.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
