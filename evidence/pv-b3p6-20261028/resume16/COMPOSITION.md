# V244 deployed/reference composition (D511)

**Correction:** Kani uses bundled rustc1.93-nightly; the rustc1.94.1 field in the original inputs was a configuration query. No passing Kani result is credited to the deployed1.94.1 configuration until reached-body/stdlib parity is checked. The following are candidate associations, not completed reclassifications. No endpoint premise is removed. V370 / pending owner D381,D386 is retained. The simulator, observer, trust-list T and op227 endpoint are unchanged.

A checked Kani gate establishes equality of the frozen source body and owned reference as interpreted by its bundled backend on the stated input domain. Transferring this to deployed1.94.1 requires the pending reached-body/stdlib parity gate. The unchanged pinned extraction provenance binds that reference body to its extracted Lean definition. The already compiled reference/context link then composes with the equality. After the pending backend/body-parity check, this would be an **owner fifth amendment reclassification**, with Kani as **P6 tool trust**; where used, a shared callee's separate extraction row is cited in SHARED-CALLEES.json. No distinct host/reference callee is stubbed as though it were the same function.

## Passing P6 components — deployed credit withheld

| Function | Native equality | Reference/context link | Domain obligation |
|---|---|---|---|
| host selector_mask_sum_16 | K72106–K72112, seven constant-mask PASS gates with symbolic raw field limbs | PV_B3P_Correct14227.mask_direct14 and native_mask_link14; immutable reference extraction | DOMAINS.json checks its only caller and all 64 frozen table cells; K72120 checks the table symbolically |
| statement selector_mask_sum_16 (ancillary separate copy) | K72113–K72119, same seven masks over symbolic limbs | same reference link; separate source hashes and full source module included verbatim | its separate only caller and 64 table cells checked in DOMAINS.json |
| reconstruct_10 | K72122, full raw array-of-16 input domain | PV_B3P_Binding13227.reconstruct_link13, source_reconstruct; immutable reference extraction | none beyond the fixed array type; every accessed index is valid |

The helper equality is **not** asserted for every u16 mask: the reference panics outside seven masks. The deployed helper's zero behavior and greater-than-eight-bit complement behavior remain general Rust behavior, not silently discarded. The closed call-domain obligation makes the seven-mask link sufficient for the actual deployed callers. The old refuted mask=0 and legacy49 constructor instances remain superseded under ruling (v).

## Conditional candidates

Canonical-only gates, even if PASS, do not close their source association until `PV_B3P_Link_callers_canonical16` is discharged at every relevant deployed caller. M31's documentation states `[0,P)`, but its public u32 representation does not enforce that invariant. No input stub or hidden assumption supplies it. Every affected row remains OPEN in CLASSIFY.json and GROUP-STATUS.md.

The raw-representative K72127 failure reports checked-MIR subtraction panics for noncanonical representatives. It is retained as a failed candidate; the release build has overflow checks off, so it is not reported as a deployed counterexample. Kani requires compiler overflow instrumentation. A successful gate must establish all its retained checks; a failed checked-MIR gate gives no release-equivalence credit.

The new standalone PV_B3P_CanonicalCalls16227 defines the open caller-domain condition and proves a nonempty model witness; audit72097 reports only propext. It proves no actual deployed caller invariant. Existing reference links and their standard-axiom audits are reused from resume13/resume14/resume15, rather than replaying unchanged Lean modules. Fresh direct Charon/Aeneas trials are not run because the prompt assigns zero non-Kani native scopes. Their acceptance/refusal status remains explicitly UNKNOWN.
