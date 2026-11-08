# PSPEC thread:f6, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `std::thread::scoped::scope`. Frozen syntax `lean/PV_THR2_F6.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f6`: Scope callback and its captures, registered entry references
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f6` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f6`: Construct the actual Scope, execute catch_unwind and callback, finish scope completion and return its result; retain panic/abort and resource branches. Both Arc instances have explicit final stores.

Construct ScopeData Arc with strong=weak=1 from CLOSED124/AtomicUsizeNew; use CLOSED126 for each actual dereference. Execute the f125 callback and source completion wait/park loop with all replies retained. Return its exact Result and explicit effects. Completion boundary never executes a lower caller suffix after div. No equality of summary/expanded activation counters.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f6` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 1782 | `thread:f121` |
| 1820 | `thread:f122` |
| 1875 | `thread:f123` |
| 1916 | `thread:f124` |
| 1989 | `thread:f125` |
| 2097 | `thread:f126` |
| 2197 | `thread:f127` |
| 2306 | `thread:f126` |
| 2404 | `thread:f128` |
| 2525 | `thread:f11` |
| 2659 | `thread:f126` |
| 2759 | `thread:f129` |
| 2935 | `thread:f130` |
| 1762 | `thread:builtin:Drop` |
| 1800 | `thread:builtin:Drop` |
| 1838 | `thread:builtin:Drop` |
| 1855 | `thread:builtin:Drop` |
| 1896 | `thread:builtin:Drop` |
| 1952 | `thread:builtin:Drop` |
| 1969 | `thread:builtin:Drop` |
| 2019 | `thread:builtin:Drop` |
| 2039 | `thread:builtin:Drop` |
| 2060 | `thread:builtin:Drop` |
| 2077 | `thread:builtin:Drop` |
| 2119 | `thread:builtin:Drop` |
| 2139 | `thread:builtin:Drop` |
| 2160 | `thread:builtin:Drop` |
| 2177 | `thread:builtin:Drop` |
| 2228 | `thread:builtin:Drop` |
| 2248 | `thread:builtin:Drop` |
| 2269 | `thread:builtin:Drop` |
| 2286 | `thread:builtin:Drop` |
| 2326 | `thread:builtin:Drop` |
| 2346 | `thread:builtin:Drop` |
| 2367 | `thread:builtin:Drop` |
| 2384 | `thread:builtin:Drop` |
| 2447 | `thread:builtin:Drop` |
| 2467 | `thread:builtin:Drop` |
| 2488 | `thread:builtin:Drop` |
| 2505 | `thread:builtin:Drop` |
| 2581 | `thread:builtin:Drop` |
| 2601 | `thread:builtin:Drop` |
| 2622 | `thread:builtin:Drop` |
| 2639 | `thread:builtin:Drop` |
| 2681 | `thread:builtin:Drop` |
| 2701 | `thread:builtin:Drop` |
| 2722 | `thread:builtin:Drop` |
| 2739 | `thread:builtin:Drop` |
| 2815 | `thread:builtin:Drop` |
| 2795 | `thread:builtin:Drop` |
| 2857 | `thread:builtin:Drop` |
| 2877 | `thread:builtin:Drop` |
| 2898 | `thread:builtin:Drop` |
| 2915 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

f6Joins has original-machine PrefixIdentity/GlobalOriginalTransport and pending DeliveryInterfaces.f125 targets; none is an inhabitant of the full contract. New spec fixes the corrected store-action machine, carries thread25, and requires complete loop initialization/preservation. Existing BeforeDelivery is retained; no successful-only BeforeReturn boundary is reintroduced.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Return callback success immediately while num_running_threads is nonzero, omitting the required wait/park path.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
