# Settlement continuation

Preparation only; no new native/Lean claim is credited until receipts exist.
Frozen source is `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

`pair_forest.rs:1748` obtains a shared reference through the actual `value()`
getter. Both validation and the lane image helper receive that SAME reference.
Under deployed features, the helper at 1772 reencodes that reference; the
`exact_bytes()` shortcut is OFF. The helper's error maps to Pool custom
`0x4153202d`, then a successful 792-byte array is boxed.

`NFR_C_SOURCE_CUT.json` retains the verbatim frozen source and helper with hashes.
`NFR_C_native.py` prepares independent actual-getter, production-capacity
Vec-to-Box, and source-exact settlement-continuation packets. Every packet keeps
original allocation identity, all eight arbitrary result projection families,
and one arbitrary byte observation; each asserted property has a corruption
control. The suffix uses local mutable records and full arbitrary child Results;
no static oracle, function pointer, multiplication, SHA or custom copy stub.

The continuation cut is NOT a bridge for earlier account/layout/marker/verify
argument admission or the enclosing process. Until those edges are proved it is
reported as suffix evidence only. The lane helper's returned typed image is
retained even though only the result reference matters to the reencoder edge.
No assumption equates arbitrary-capacity Vec pointers; the carrier cut has
capacity = length = 792, the production SDK getter domain supported by NFO's
pinned source/ELF inspection.

`NFR_CSettlement.lean` names the same value at each validation/lane/encode event,
retains every child rejection prefix and exact encoder error mapping, and
reuses the CLOSED encoder bridge after same-value identification derives its
statement domain. This is a mathematical source-cut component, not a new
runtime/SDK or enclosing caller premise discharge.
