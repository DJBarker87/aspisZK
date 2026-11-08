# PSPEC thread:f1, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains OPEN.

Source: `aspis_r1_cert_check::native_workers::ordered_map_inner`. Frozen syntax `lean/PV_THR2_F1.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f1`: n, f and worker flag; typed capture regions and public iteration bounds
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f1` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f1`: Follow the source worker/sequential branch, scope, spawn and join order and return ordered results; preserve entry capture ownership with exact handle/worker effects.

Both worker/sequential routes remain in the domain. Iterate and collect at source arguments; retain order of scope/spawn/join and append. Native iterator f9 and Vec append f10 update their SOURCE descriptors through the concrete store-action interpreter. Resource demand witness independence is an obligation to prove, not an entry restriction.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f1` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 88 | `thread:f3` |
| 126 | `thread:f4` |
| 184 | `thread:f2` |
| 215 | `thread:f5` |
| 265 | `thread:f6` |
| 317 | `thread:f7` |
| 394 | `thread:f8` |
| 487 | `thread:f9` |
| 779 | `thread:f11` |
| 930 | `thread:f10` |
| 1633 | `thread:f3` |
| 1671 | `thread:f4` |
| 64 | `thread:builtin:Drop` |
| 76 | `thread:builtin:Drop` |
| 102 | `thread:builtin:Drop` |
| 114 | `thread:builtin:Drop` |
| 143 | `thread:builtin:Drop` |
| 172 | `thread:builtin:Drop` |
| 203 | `thread:builtin:Drop` |
| 241 | `thread:builtin:Drop` |
| 253 | `thread:builtin:Drop` |
| 281 | `thread:builtin:Drop` |
| 293 | `thread:builtin:Drop` |
| 305 | `thread:builtin:Drop` |
| 334 | `thread:builtin:Drop` |
| 346 | `thread:builtin:Drop` |
| 358 | `thread:builtin:Drop` |
| 370 | `thread:builtin:Drop` |
| 382 | `thread:builtin:Drop` |
| 415 | `thread:builtin:Drop` |
| 427 | `thread:builtin:Drop` |
| 439 | `thread:builtin:Drop` |
| 451 | `thread:builtin:Drop` |
| 463 | `thread:builtin:Drop` |
| 475 | `thread:builtin:Drop` |
| 646 | `thread:builtin:Drop` |
| 526 | `thread:builtin:Drop` |
| 538 | `thread:builtin:Drop` |
| 550 | `thread:builtin:Drop` |
| 562 | `thread:builtin:Drop` |
| 574 | `thread:builtin:Drop` |
| 586 | `thread:builtin:Drop` |
| 598 | `thread:builtin:Drop` |
| 610 | `thread:builtin:Drop` |
| 622 | `thread:builtin:Drop` |
| 634 | `thread:builtin:Drop` |
| 659 | `thread:builtin:Drop` |
| 671 | `thread:builtin:Drop` |
| 683 | `thread:builtin:Drop` |
| 695 | `thread:builtin:Drop` |
| 707 | `thread:builtin:Drop` |
| 719 | `thread:builtin:Drop` |
| 731 | `thread:builtin:Drop` |
| 743 | `thread:builtin:Drop` |
| 755 | `thread:builtin:Drop` |
| 767 | `thread:builtin:Drop` |
| 822 | `thread:builtin:Drop` |
| 834 | `thread:builtin:Drop` |
| 846 | `thread:builtin:Drop` |
| 858 | `thread:builtin:Drop` |
| 870 | `thread:builtin:Drop` |
| 882 | `thread:builtin:Drop` |
| 894 | `thread:builtin:Drop` |
| 906 | `thread:builtin:Drop` |
| 918 | `thread:builtin:Drop` |
| 1041 | `thread:builtin:Drop` |
| 945 | `thread:builtin:Drop` |
| 957 | `thread:builtin:Drop` |
| 969 | `thread:builtin:Drop` |
| 981 | `thread:builtin:Drop` |
| 993 | `thread:builtin:Drop` |
| 1005 | `thread:builtin:Drop` |
| 1017 | `thread:builtin:Drop` |
| 1029 | `thread:builtin:Drop` |
| 1138 | `thread:builtin:Drop` |
| 1054 | `thread:builtin:Drop` |
| 1066 | `thread:builtin:Drop` |
| 1078 | `thread:builtin:Drop` |
| 1090 | `thread:builtin:Drop` |
| 1102 | `thread:builtin:Drop` |
| 1114 | `thread:builtin:Drop` |
| 1126 | `thread:builtin:Drop` |
| 1223 | `thread:builtin:Drop` |
| 1151 | `thread:builtin:Drop` |
| 1163 | `thread:builtin:Drop` |
| 1175 | `thread:builtin:Drop` |
| 1187 | `thread:builtin:Drop` |
| 1199 | `thread:builtin:Drop` |
| 1211 | `thread:builtin:Drop` |
| 1314 | `thread:builtin:Drop` |
| 1242 | `thread:builtin:Drop` |
| 1254 | `thread:builtin:Drop` |
| 1266 | `thread:builtin:Drop` |
| 1278 | `thread:builtin:Drop` |
| 1290 | `thread:builtin:Drop` |
| 1302 | `thread:builtin:Drop` |
| 1389 | `thread:builtin:Drop` |
| 1329 | `thread:builtin:Drop` |
| 1341 | `thread:builtin:Drop` |
| 1353 | `thread:builtin:Drop` |
| 1365 | `thread:builtin:Drop` |
| 1377 | `thread:builtin:Drop` |
| 1450 | `thread:builtin:Drop` |
| 1402 | `thread:builtin:Drop` |
| 1414 | `thread:builtin:Drop` |
| 1426 | `thread:builtin:Drop` |
| 1438 | `thread:builtin:Drop` |
| 1501 | `thread:builtin:Drop` |
| 1465 | `thread:builtin:Drop` |
| 1477 | `thread:builtin:Drop` |
| 1489 | `thread:builtin:Drop` |
| 1538 | `thread:builtin:Drop` |
| 1514 | `thread:builtin:Drop` |
| 1526 | `thread:builtin:Drop` |
| 1564 | `thread:builtin:Drop` |
| 1552 | `thread:builtin:Drop` |
| 1577 | `thread:builtin:Drop` |
| 1609 | `thread:builtin:Drop` |
| 1621 | `thread:builtin:Drop` |
| 1647 | `thread:builtin:Drop` |
| 1659 | `thread:builtin:Drop` |
| 1688 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

The pinned ledger has no complete compiled Pre/Post contract for this OPEN row. Prefix helpers are supporting evidence only. The common clauses supply the machine, reference/OWNER/numbering invariants, first boundary, all-answer observation and frame. No existing theorem is being silently restated as a full proof.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Return results in reverse index order when two worker results differ.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
