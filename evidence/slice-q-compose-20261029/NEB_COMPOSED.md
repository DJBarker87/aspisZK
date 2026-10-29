# Slice Q composition checkpoint

The two requested slice-root theorems are **not yet established**:

- `crates/aspis-r1-cost-probe/src/candidate.rs::query_loop`: OPEN.
- `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: OPEN.

No full native root statement is represented by a tautological bridge hypothesis or a new generic execution evaluator. The current certified subtrees are the private full-u64 reducer and its actual M31 wrapper: **four inventory occurrence rows CLOSED** (`TX1:045`, `TX2:026`, `TX1:020`, `TX2:014`) under the NDT extension's root-domain semantics. One real internal edge is CLOSED. Both complete slice roots remain OPEN. Historical local bridge classifications are preserved.

## Reducer subtree statement and retained hypotheses

For either frozen scalar root, every typed u64 input has the cohort result `Ok z`, where `z.val = x.val % 2147483647` and `z.val < 2147483647`; ambient state is unchanged and ordered effects are empty. The native half is K001/K007 with K002/K008 controls and scalar fidelity K003–K006. The independent reference is E002. The kernel-checked model equations are L021, `NEB_ReducerCall.reference`, `wrapper`, `value`, `state_effects`, and `all_domain`.

The hybrid theorem retains only that subtree root's own PacketDomain (all typed u64), its own PhysicalInterpretation (typed scalar/newtype source/runtime representation), and approved `NativeContractSemanticTransport`. This is the owner's P6/D188 **trust reclassification, never removal**. There is no inner PacketDomain, inner PhysicalInterpretation or successful-return premise. The exact caller passes `value` unchanged and wraps the scalar reply in the sole M31 field. The external inventory constructor entry is classified explicitly; no constructor trust row is added. See NEB_REDUCER_ASSOCIATION.md for the native/state/carrier audit.

Full checked Lean statements:

```lean
theorem all_domain (x : U64) : PacketDomain x
-- PacketDomain x := x.val < 18446744073709551616

theorem reference (x : U64) :
  NEB_Reference.reference x = FIo_Native.aspis_core.field.reduce_u64 x

theorem wrapper (x : U64) :
  FIo_Native.aspis_core.field.M31.reduce_u64 x = NEB_Reference.reference x

theorem value (x : U64) : ∃ z : U32,
  NEB_Reference.reference x = ok z ∧
  FIo_Native.aspis_core.field.M31.reduce_u64 x = ok z ∧
  z.val = x.val % 2147483647 ∧ z.val < 2147483647

theorem state_effects {S Event : Type} (s : S) (x : U64) : ∃ z : U32,
  withState (Event := Event) s (NEB_Reference.reference x) = ok (z,s,[]) ∧
  withState (Event := Event) s
    (FIo_Native.aspis_core.field.M31.reduce_u64 x) = ok (z,s,[]) ∧
  z.val = x.val % 2147483647 ∧ z.val < 2147483647
```

`withState` is the pure Result lift, not an invented native evaluator. Native purity is independently checked against the frozen pointerless numeric bodies and transparent constructor.

L021 `#print axioms`:

- `NEB_ReducerCall.all_domain`: `[propext, Quot.sound]`.
- `NEB_ReducerCall.reference`: `[propext, Classical.choice, Quot.sound]`.
- `NEB_ReducerCall.wrapper`: `[propext, Classical.choice, Quot.sound]`.
- `NEB_ReducerCall.value`: `[propext, Classical.choice, Quot.sound]`.
- `NEB_ReducerCall.state_effects`: `[propext, Classical.choice, Quot.sound]`.

## Other checked progress, not native composition credit

The accepted query_loop model now exports every reached query's geometry-accessor index domain, from its actual accepted call sequence. The installed opening's exact 832-byte return is derived from that same query's array read and actual op11; no independent opening success is assumed. Field/WideExact intermediate witnesses derive later canonical domains from earlier exact Results. Checked scalar acceptance establishes canonicality without assuming it on the raw scalar. These partial certificates do not close their native rows.

All 257 internal edges remain explicit in NEB_EDGES.json, with certificates or current obstacles, selected packet domains and inventory calls. Conservative receiver alternatives are recorded, not silently pruned. Source audit identifies slice-boundary M31::neg, CM31::is_zero, CM31::square and the inv_with inverse argument. No out-of-slice bridge is developed.

No headline premise, 100-bit bound, privacy property, or two-transaction law is removed. No shipped Rust/Lean source, release ELF or session A worktree is changed.
