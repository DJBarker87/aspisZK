# PSPEC thread:f361, revision 1

Status: SPECIFICATION ONLY; frozen by FREEZE.json. Ledger remains PARTIAL.

Source: `std::thread::lifecycle::spawn_unchecked`. Frozen syntax `lean/PV_THR2_F361.lean` at `0ba0c659c9bc5fc446e4ac4cd09f0e145339f1f1` on `codex/pv-evhB-20261103`. Exact signature and call metadata: DEPENDENCIES.json. Source artifact is retained compressed in inputs/.

## Pre and named machine

`Pre_thread_f361`: Builder, closure/captures and scope; entry-owned registered regions and typed representations
Conjoin ALL entry clauses in PSPEC_COMMON.md, using the actual typed arguments and arbitrary lower/suspended callers. `MachineSpec_thread_f361` is the common machine specification specialized to this pinned body and the slots below. No child-success, future read, decode-success, activation-counter equality or desired-store hypothesis.

## Post, frame and complete arms

`Post_thread_f361`: Construct Thread, Packet Arc and worker closure; register and allocate the ThreadInit box at 14756 with its actual fields from source stores. Retain all later return/spawn effects and all failure branches; OwnInit is a marked intermediate milestone, not the function return.

The full function boundary is AFTER spawn_unchecked returns, not at OwnInit. Entry includes W3 NameEntryValidity.NameOwned (both Option constructors, UTF8 bytes, registry and validity) and ScopeEntryValidity.Shape. Track Thread/CString, Packet Arc, callback Box allocation13923, casts14119/14121, Unique/Box wrappers and ThreadInit allocation14756. At14756 derive decodeBridged from the actual registry/vtable bridge; consume allBridged and SourceInitBoxOwnership. Preserve the later spawn success AND Err arms and every earlier allocation prefix.

Every returned Ok AND Err payload, fault, process abort, divergence and ACTUAL pending answer obeys PSPEC_COMMON.md. `Frame_thread_f361` is its source-cell/heap/OWNER/event frame at THIS row's completion or delivery, never beyond it. Abort has event prefix only. Allocation and reservation are explicit environment replies. Each transitive reached allocating child retains allocation-before-later-Err and allocation-before-log arms; no blanket may-abort alternative.

## Child slots at source call sites

| Site | Required child |
|---|---|
| 12111 | `thread:f295` |
| 12199 | `thread:f452` |
| 12290 | `thread:f213` |
| 12399 | `thread:f453` |
| 12509 | `thread:f454` |
| 12668 | `thread:f455` |
| 12801 | `thread:f124` |
| 12950 | `thread:f360` |
| 13123 | `thread:f456` |
| 13323 | `thread:f126` |
| 13522 | `thread:f126` |
| 13713 | `thread:f457` |
| 13923 | `thread:builtin:"BoxNew"` |
| 14113 | `thread:f443` |
| 14313 | `thread:f458` |
| 14535 | `thread:f214` |
| 14756 | `thread:builtin:"BoxNew"` |
| 14976 | `thread:f459` |
| 15189 | `thread:f279` |
| 15411 | `thread:f280` |
| 12045 | `thread:builtin:Drop` |
| 12067 | `thread:builtin:Drop` |
| 12089 | `thread:builtin:Drop` |
| 12133 | `thread:builtin:Drop` |
| 12155 | `thread:builtin:Drop` |
| 12177 | `thread:builtin:Drop` |
| 12224 | `thread:builtin:Drop` |
| 12246 | `thread:builtin:Drop` |
| 12268 | `thread:builtin:Drop` |
| 12314 | `thread:builtin:Drop` |
| 12333 | `thread:builtin:Drop` |
| 12355 | `thread:builtin:Drop` |
| 12377 | `thread:builtin:Drop` |
| 12424 | `thread:builtin:Drop` |
| 12443 | `thread:builtin:Drop` |
| 12465 | `thread:builtin:Drop` |
| 12487 | `thread:builtin:Drop` |
| 12542 | `thread:builtin:Drop` |
| 12561 | `thread:builtin:Drop` |
| 12583 | `thread:builtin:Drop` |
| 12602 | `thread:builtin:Drop` |
| 12624 | `thread:builtin:Drop` |
| 12646 | `thread:builtin:Drop` |
| 12694 | `thread:builtin:Drop` |
| 12716 | `thread:builtin:Drop` |
| 12735 | `thread:builtin:Drop` |
| 12757 | `thread:builtin:Drop` |
| 12779 | `thread:builtin:Drop` |
| 12824 | `thread:builtin:Drop` |
| 12843 | `thread:builtin:Drop` |
| 12865 | `thread:builtin:Drop` |
| 12884 | `thread:builtin:Drop` |
| 12906 | `thread:builtin:Drop` |
| 12928 | `thread:builtin:Drop` |
| 12975 | `thread:builtin:Drop` |
| 12997 | `thread:builtin:Drop` |
| 13016 | `thread:builtin:Drop` |
| 13038 | `thread:builtin:Drop` |
| 13057 | `thread:builtin:Drop` |
| 13079 | `thread:builtin:Drop` |
| 13101 | `thread:builtin:Drop` |
| 13153 | `thread:builtin:Drop` |
| 13175 | `thread:builtin:Drop` |
| 13197 | `thread:builtin:Drop` |
| 13216 | `thread:builtin:Drop` |
| 13238 | `thread:builtin:Drop` |
| 13257 | `thread:builtin:Drop` |
| 13279 | `thread:builtin:Drop` |
| 13301 | `thread:builtin:Drop` |
| 13352 | `thread:builtin:Drop` |
| 13374 | `thread:builtin:Drop` |
| 13396 | `thread:builtin:Drop` |
| 13415 | `thread:builtin:Drop` |
| 13437 | `thread:builtin:Drop` |
| 13456 | `thread:builtin:Drop` |
| 13478 | `thread:builtin:Drop` |
| 13500 | `thread:builtin:Drop` |
| 13543 | `thread:builtin:Drop` |
| 13565 | `thread:builtin:Drop` |
| 13587 | `thread:builtin:Drop` |
| 13606 | `thread:builtin:Drop` |
| 13628 | `thread:builtin:Drop` |
| 13647 | `thread:builtin:Drop` |
| 13669 | `thread:builtin:Drop` |
| 13691 | `thread:builtin:Drop` |
| 13753 | `thread:builtin:Drop` |
| 13775 | `thread:builtin:Drop` |
| 13797 | `thread:builtin:Drop` |
| 13816 | `thread:builtin:Drop` |
| 13838 | `thread:builtin:Drop` |
| 13857 | `thread:builtin:Drop` |
| 13879 | `thread:builtin:Drop` |
| 13901 | `thread:builtin:Drop` |
| 13943 | `thread:builtin:Drop` |
| 13965 | `thread:builtin:Drop` |
| 13987 | `thread:builtin:Drop` |
| 14006 | `thread:builtin:Drop` |
| 14028 | `thread:builtin:Drop` |
| 14047 | `thread:builtin:Drop` |
| 14069 | `thread:builtin:Drop` |
| 14091 | `thread:builtin:Drop` |
| 14143 | `thread:builtin:Drop` |
| 14165 | `thread:builtin:Drop` |
| 14187 | `thread:builtin:Drop` |
| 14206 | `thread:builtin:Drop` |
| 14228 | `thread:builtin:Drop` |
| 14247 | `thread:builtin:Drop` |
| 14269 | `thread:builtin:Drop` |
| 14291 | `thread:builtin:Drop` |
| 14343 | `thread:builtin:Drop` |
| 14365 | `thread:builtin:Drop` |
| 14387 | `thread:builtin:Drop` |
| 14409 | `thread:builtin:Drop` |
| 14428 | `thread:builtin:Drop` |
| 14450 | `thread:builtin:Drop` |
| 14469 | `thread:builtin:Drop` |
| 14491 | `thread:builtin:Drop` |
| 14513 | `thread:builtin:Drop` |
| 14564 | `thread:builtin:Drop` |
| 14586 | `thread:builtin:Drop` |
| 14608 | `thread:builtin:Drop` |
| 14630 | `thread:builtin:Drop` |
| 14649 | `thread:builtin:Drop` |
| 14671 | `thread:builtin:Drop` |
| 14690 | `thread:builtin:Drop` |
| 14712 | `thread:builtin:Drop` |
| 14734 | `thread:builtin:Drop` |
| 14784 | `thread:builtin:Drop` |
| 14806 | `thread:builtin:Drop` |
| 14828 | `thread:builtin:Drop` |
| 14850 | `thread:builtin:Drop` |
| 14869 | `thread:builtin:Drop` |
| 14891 | `thread:builtin:Drop` |
| 14910 | `thread:builtin:Drop` |
| 14932 | `thread:builtin:Drop` |
| 14954 | `thread:builtin:Drop` |
| 14997 | `thread:builtin:Drop` |
| 15019 | `thread:builtin:Drop` |
| 15041 | `thread:builtin:Drop` |
| 15063 | `thread:builtin:Drop` |
| 15082 | `thread:builtin:Drop` |
| 15104 | `thread:builtin:Drop` |
| 15123 | `thread:builtin:Drop` |
| 15145 | `thread:builtin:Drop` |
| 15167 | `thread:builtin:Drop` |
| 15219 | `thread:builtin:Drop` |
| 15241 | `thread:builtin:Drop` |
| 15263 | `thread:builtin:Drop` |
| 15285 | `thread:builtin:Drop` |
| 15304 | `thread:builtin:Drop` |
| 15326 | `thread:builtin:Drop` |
| 15345 | `thread:builtin:Drop` |
| 15367 | `thread:builtin:Drop` |
| 15389 | `thread:builtin:Drop` |
| 15554 | `thread:builtin:Drop` |
| 15447 | `thread:builtin:Drop` |
| 15469 | `thread:builtin:Drop` |
| 15488 | `thread:builtin:Drop` |
| 15510 | `thread:builtin:Drop` |
| 15532 | `thread:builtin:Drop` |
| 15642 | `thread:builtin:Drop` |
| 15576 | `thread:builtin:Drop` |
| 15598 | `thread:builtin:Drop` |
| 15620 | `thread:builtin:Drop` |

Each BODY call is one D877 summary step at the same arguments, with a graph-of-function child law. The map supplies the CLOSED root or explicitly flags the gap. Call-domain discharge belongs to this row, not an extra hypothesis. Named leaf semantics and runtime adequacy remain in their recorded inventory.

## Comparison to current package statements

f361Statement has sourceStep and changes parameters, original IntrinsicState executions, scopeOwned conditional shape and Pre without the final typed NameEntryValidity/numbering clauses. New spec binds the actual enlarged interpreter, source write meanings and name/Scope entry validity, requires concrete source/binary bridge adequacy and all joins to return. Old statement and its later helper extensions remain unchanged.

Common before/after differences for ALL rows: the ledger's drafted return boundary is bounded by own completion/delivery; process abort loses post-abort state; OWNER has fresh-frame, non-null/alignment and native-ghost framing clauses; entry has live numbering; cross-callee Store/counter equality is removed. These are thread23'/slice9/10/11'/thread25/27 corrections to interface form, with the actual source behavior retained. Existing CLOSED rows are not edited or withdrawn.

## Rejection example

Allocate a ThreadInit containing a constant callback pointer rather than the actual callback Box data/vtable.

This is a normative counterimplementation example, not a new compiled counterexample theorem. Resource replies in the example grant the requests needed to reach the distinguishing output; that is an admissible environment, not a success restriction on this specification.
