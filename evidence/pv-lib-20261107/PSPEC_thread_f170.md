# PSPEC thread:f170, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `std::thread::local::impl[inherent]::try_with`. Frozen syntax `lean/PV_THR2_F170.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f170`: LocalKey reference and callback with its recorded captures
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f170` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f170`: Select the source initializer token, consume its arbitrary reply, and invoke the actual callback on the returned TLS reference; return the Result and retain every failure or missing-representation branch.

Both getter and setter contexts must be covered by the same row. Source TLS initializer468/469, Option as_ref277/ok_or278, Result branch279/from_residual280 and callback dispatch use provider constructors by name. Pure leaves preserve world on every answer (thread24). The setter executes f207 and the f289 concrete source-cell write; no arbitrary Effects field or write-definedness premise is admitted in MachineSpec.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f170` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 8039 | `thread:f468` |
| 8039 | `thread:f469` |
| 8056 | `thread:f277` |
| 8074 | `thread:f278` |
| 8091 | `thread:f279` |
| 8113 | `thread:f280` |
| 8162 | `thread:f18` |
| 8030 | `thread:builtin:Drop` |
| 8047 | `thread:builtin:Drop` |
| 8065 | `thread:builtin:Drop` |
| 8082 | `thread:builtin:Drop` |
| 8104 | `thread:builtin:Drop` |
| 8123 | `thread:builtin:Drop` |
| 8153 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

f170Statement takes arbitrary Effects D, has an older partial numbering Pre, and summary outcomes rather than a proved actual corrected-machine execution. OriginalStatement adds resolver/request equations but still targets the original interpreter; source-store interpreter later helpers remain conditional on local path/age facts. New spec derives those facts internally, binds the concrete write meaning and no write-definedness/Store premise. It uses exact source constructor facets and every pending boundary.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Invoke the setter but restore the old Cell afterward; generic reachable-effects summaries can permit this, the source specification cannot.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
