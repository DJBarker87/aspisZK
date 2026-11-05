# Failing steps

## Native seed preflight
Own input error: host output directory absent. Fixed before admission and launch; original log retained. No prover ran.

## Item 1: NHP_K003 unrestricted physical splitter window
Actual frozen splitter, dynamic returning allocation 4..isize::MAX, four arbitrary hint bytes and selected body cell. Exit 1; 9 failed checks (3 unreachable), including selected body value, suffix frame and hints 1..3. No timeout or memory kill. Source and full receipt pinned per attempt.
Classification: unisolated native/tool representation or harness-domain mismatch, NOT a claimed source defect. NHC_K119 previously failed unrestricted iterator geometry; neither is production credit. Next isolate pre-call writes/reads without the splitter; do not rerun this shape unchanged. No restricted allocation bound becomes a production premise.

## Item 1: NHP_K004 storage isolation
Removed the actual splitter entirely, retaining allocation, selected-cell/suffix stores and pre-call loads. Exit 1: all five storage assertions fail. This isolates the K003 obstruction before any frozen splitter code; source bug attribution is rejected. Exact object-offset representation and validity domain remain to be isolated. No bounded substitute is promoted to arbitrary production input.

## Item 2: NHP_K005 own snapshot typing
Compiler E0507: snapshot tried to move an &mut u64 through Ref. Corrected to copy the u64 through double dereference. K006 then passed; K007 wrong-error control failed. This is an input repair, not a proof failure or resource-limit replay.

## Item 1: NHP_K026 ProgramResult equality contract
CBMC timed out at the unchanged 90-second limit (exit 1; wall 93.43s; peak RSS 479944 KiB; swaps 0). No credit and no same-shape rerun. Replacement K027 uses explicit constructor/Custom-code discrimination, eliminating derived ProgramError equality (including foreign String comparison) from the contract. Actual guard body, height domain and error are unchanged. This is an interface split under (ak); no timeout or cap increase.

## SDK reference model: NHP_L018 decoded_known
Deterministic whnf heartbeat timeout at the nested-if decoder known-range proof (22.84s,5680312KiB). No cap/heartbeat increase and no unchanged rerun. The replacement uses a linear constructor match, preserving the exact26-class table. Failed dependent elaborations printed sorryAx and are explicitly excluded; only a successful replacement module may be imported/audited.

## Marker system-owned empty, active exclusive data borrow: K086
Actual classify_nullifier_marker_account_v1, valid Rust AccountInfo with System owner, empty data, valid privileges, program!=System, live RefMut data guard. Proposed Err(AccountBorrowFailed) result fails: the source uses data_is_empty(), which invokes infallible RefCell::borrow and panics on this prestate. This is a real mismatch with that proposed total Result specification, not a demonstrated production source bug. The caller must prove borrowability before the System-empty branch (and after any creation CPI), or model the abort prefix explicitly. Do not substitute try_borrow_data semantics or silently impose a zero-counter production premise. Exact failure and untouched source retained.

K086 native failure diagnostic is the unsupported runtime-formatted panic-message check. Source inspection of the infallible borrow, plus the live RefMut prestate and that reached panic path, supports the mismatch; the Kani failure alone is not labelled a successful panic-semantics proof.

## Additional input rejections retained
K068: stale patch after a generator wildcard-parser failure; requested SDK harness absent, no semantic credit. K095: Rc frame probe used std in no_std code; fixed to alloc with identical/stronger checks, corrected K096 passes. No timeout or memory-killed shape was rerun unchanged.

## Final remaining stage assertions
See NHP_REMAINING.md: successful same-account decoder/PDA, actual all/any/source-parent, CPI modified ranges, same decoded-request payment and registry/meta associations are missing callee/native laws. They are OPEN, not passes. There is no evidence of a frozen-source storage bug from K003/K004. K086 is a mismatch in the proposed total Result specification on its stated prestate; production reachability remains open.
