# Slice Q composition checkpoint

The two requested slice-root theorems are **not yet established**:

- `crates/aspis-r1-cost-probe/src/candidate.rs::query_loop`: OPEN.
- `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: OPEN.

No full native root statement is represented by a tautological bridge hypothesis or a new generic execution evaluator. The certified reducer and additive subtrees now give **24 inventory occurrence rows CLOSED**, **27 of 257 slice internal edges CLOSED**, and six additional original NDT conservative self-obligations explicitly CLOSED. Both requested complete slice roots remain OPEN. Both complete slice roots remain OPEN. Historical local bridge classifications are preserved.

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

## Additive subtree statements (L039)

The ten frozen native methods and their controls are indexed in NEB_ADDITIVE_ASSOCIATION.md. The only hybrid transport qualifications are the root's own canonical PacketDomain, root PhysicalInterpretation and approved NativeContractSemanticTransport (P6/D188 option-A reclassification). No non-root named hypothesis remains. These checked Lean statements expose every model input, return, state and ordered effect; native/reference transport is separately tied to the exact frozen methods in the content-addressed native review. `NEB_PureFrame.run` is a pure model lift, not a native evaluator.

```lean
theorem m_add {S Event : Type} (state : S) (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y=ok z ∧
      NEB_AdditiveRef.add_word (x) (y)=ok (z) ∧ z.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.M31.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add_word (x) (y))=ok (z,state,[])
```

```lean
theorem m_sub {S Event : Type} (state : S) (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y=ok z ∧
      NEB_AdditiveRef.sub_word (x) (y)=ok (z) ∧ z.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.M31.sub x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub_word (x) (y))=ok (z,state,[])
```

```lean
theorem m_double {S Event : Type} (state : S) (x : U32) (hx : x.val<2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.double x=ok z ∧
      NEB_AdditiveRef.add_word (x) (x)=ok (z) ∧ z.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.M31.double x)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add_word (x) (x))=ok (z,state,[])
```

```lean
theorem cm_add {S Event : Type} (state : S) (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y=ok z ∧
      NEB_AdditiveRef.add2 (wordsC x) (wordsC y)=ok (wordsC z) ∧ canonC z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add2 (wordsC x) (wordsC y))=ok (wordsC z,state,[])
```

```lean
theorem cm_sub {S Event : Type} (state : S) (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y=ok z ∧
      NEB_AdditiveRef.sub2 (wordsC x) (wordsC y)=ok (wordsC z) ∧ canonC z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.sub x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub2 (wordsC x) (wordsC y))=ok (wordsC z,state,[])
```

```lean
theorem cm_double {S Event : Type} (state : S) (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.CM31.double x=ok z ∧
      NEB_AdditiveRef.add2 (wordsC x) (wordsC x)=ok (wordsC z) ∧ canonC z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.double x)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add2 (wordsC x) (wordsC x))=ok (wordsC z,state,[])
```

```lean
theorem qm_add {S Event : Type} (state : S) (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.add x y=ok z ∧
      NEB_AdditiveRef.add4 (wordsQ x) (wordsQ y)=ok (wordsQ z) ∧ canonQ z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add4 (wordsQ x) (wordsQ y))=ok (wordsQ z,state,[])
```

```lean
theorem qm_sub {S Event : Type} (state : S) (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.sub x y=ok z ∧
      NEB_AdditiveRef.sub4 (wordsQ x) (wordsQ y)=ok (wordsQ z) ∧ canonQ z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.sub x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub4 (wordsQ x) (wordsQ y))=ok (wordsQ z,state,[])
```

```lean
theorem wide_add {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok z ∧
      NEB_AdditiveRef.add8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.add x y)=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.add8 (wordsE x) (wordsE y))=ok (wordsE z,state,[])
```

```lean
theorem wide_sub {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z : NE,
      AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y)=ok (NBG_GetterPorts.wide z) ∧
      NEB_AdditiveRef.sub8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z ∧
      NEB_PureFrame.run (Event:=Event) state (AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y))=ok (NBG_GetterPorts.wide z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub8 (wordsE x) (wordsE y))=
        ok (wordsE z,state,[])
```

Axioms, exact audited output:

```text
'NEB_AdditiveFrames.m_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.m_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.m_double' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.cm_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.cm_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.cm_double' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.qm_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.qm_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.wide_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'NEB_AdditiveFrames.wide_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All conservative targets and cfg-inactive inventory occurrences remain present. Missing/wrong certificates leave affected rows OPEN; the added mutation suite has 28 passing tests. The original NDT ledger is unchanged.
