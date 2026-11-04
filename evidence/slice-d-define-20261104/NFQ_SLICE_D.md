# Slice D definition

**Definition and inherited status only. Target not yet established.**

Frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Baseline: NFK ledger (587 occurrences). D has **291 functions, 441 internal edges, 339 inventory rows**: {'OPEN': 339}.

## Exact deployed roots

Both transaction roots are `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction`. With deployed `pool-adapter`, TX1 instruction `[3,10]` or `[3,11]` dispatches through `pool_route::admitted`, `r1_pool_adapter::process`, `r1_pool_adapter_owned::stage1` / `stage1_owned`, and `lib.rs::first_decoded` to `candidate::tx1`. TX2 `[4]` dispatches through the same entry/adapter to `stage2` / `stage2_owned`, then `candidate::tx2_authenticated` / `tx2_common`. There is no separate deployed lib.rs second entry. `lib.rs::first` and direct `candidate::tx2` are in the disabled non-pool-adapter branch and absent from the frozen inventory.

The function set is the union of per-transaction canonical closures minus the Q/S function sets. Q/S roots are opaque certification boundaries; their recorded descendants are used only to compute original inventory membership. No traversal through discovery mentions. Receiver-resolution overapproximations and recursive edges remain exactly as inventoried. Internal edges use the same sorted `caller -> callee` representation as VERTICAL-SLICES.

## Inherited evidence is not new closure

Twelve of the thirteen opaque leaf functions are in D (canonical::Dot::push is in Q). All 12 remain OPEN composed rows in NFK; local leaf restoration alone supplies no new CLOSED row. NFQ_LEAVES.json records every one of the 13 opaque packets and KNF K-2 status. KNF restores four affected local bridges; all 13 retain their local-domain credit. This does not establish every caller domain or repair writable-static support. The NFK composed statuses above remain authoritative. DrvI provides counterexamples to arbitrary-driver identity, not native closure; DrvC constructs the installed model and retires L160 only. Neither packet closes a new NDT occurrence here.

Later NFN removes the two geometry qualifications; NFM reports closed dots. Those functions belong to Q and remain separate from this D baseline. No duplicate row credit. RuntimeReturnData and RuntimeMemcmp are owner-accepted trust rows as of 2026-11-04; NFK historical pending wording is superseded, not discharged.

## Slice boundary findings

The Pool settlement consumer is not a node of the frozen 587-row verifier inventory. It cannot be silently added using this schema/tooling. Sibling NFO owns its native return-data packet. Pool-side settlement and same-instruction association remain explicit external boundaries.

The canonical graph omits the error callback edge (see NFQ_COVERAGE.md). No source/cfg(kani) file changed; no ELF rebuild trigger.
