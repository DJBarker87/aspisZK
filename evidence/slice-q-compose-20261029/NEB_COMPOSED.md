# Slice Q composition checkpoint

The two requested slice-root theorems are **not yet established**:

- `crates/aspis-r1-cost-probe/src/candidate.rs::query_loop`: OPEN.
- `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: OPEN.

No full native root statement is represented by a tautological bridge hypothesis or a new generic execution evaluator. The certified reducer and additive subtrees now give **60 inventory occurrence rows CLOSED**, **103 of 257 slice internal edges CLOSED**, and eleven additional original NDT conservative self-obligations explicitly CLOSED. Both requested complete slice roots remain OPEN. Both complete slice roots remain OPEN. Historical local bridge classifications are preserved.

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

## Representation, field and actual-cohort carrier checkpoint

The current total is 60 CLOSED occurrence rows and 103/257 CLOSED edges. The two requested roots remain OPEN. The domain theorems below carry their own stated typed/canonical input domain; pure state/effect lifts are tied to the reviewed frozen native body separately. Field multiplication follows the adopted translation law and inherited conditional packets, not a new Kani multiplication claim. The only hybrid qualifications retained for each closed subtree root are its own PacketDomain, its own PhysicalInterpretation, approved runtime trust where reached and NativeContractSemanticTransport (option-A reclassification, never removal). Full source statements and every printed axiom follow. Failed attempts are retained but excluded.

### NEB_GeometryGatherDomains (L042)

```lean
import NEB_GeometryIndices
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryGatherDomains
open Aeneas Aeneas.Std Result ControlFlow AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

theorem step {CoreError : Type} (ops : Ops CoreError) (error : CoreError) (start : Usize)
    (iter iter1 iterOut : core.slice.iter.Iter U32) (query : U32)
    (zs zsOut flat flatOut : alloc.vec.Vec U32)
    (next : core.slice.iter.IteratorSliceIter.next iter=ok (some query,iter1))
    (run : verifier.QueryGeometry.for_range_loop0.body
      (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
      start iter zs flat=ok (cont (iterOut,zsOut,flatOut))) :
    ∃ (r : Port4C_GeometryGather.Row) (u parent left right fibre fleft fright : Usize)
      (point : aspis_core.r0.domain.Point U32) (square doubled one : U32),
      iterOut=iter1 ∧
      lift (UScalar.cast .Usize query)=ok u ∧
      NEB_GeometryIndices.indexPort error u=ok (.Ok fibre) ∧ fibre=u ∧ fibre.val<262144 ∧
      (NEB_GeometryIndices.install ops error).op15 fibre=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      u/4#usize=ok parent ∧ left=Usize.wrapping_mul parent 4#usize ∧
      NEB_GeometryIndices.indexPort error left=ok (.Ok fleft) ∧ fleft=left ∧ fleft.val<262144 ∧
      (NEB_GeometryIndices.install ops error).op14 fleft=ok r.lineX ∧ r.lineX.val<2147483647 ∧
      right=Usize.wrapping_add left 3#usize ∧
      NEB_GeometryIndices.indexPort error right=ok (.Ok fright) ∧ fright=right ∧ fright.val<262144 ∧
      (NEB_GeometryIndices.install ops error).op14 fright=ok r.lineY ∧ r.lineY.val<2147483647 ∧
      r.x=point.x ∧ r.y=point.y ∧
      (NEB_GeometryIndices.install ops error).op9 r.lineX r.lineX=ok square ∧ square.val<2147483647 ∧
      (NEB_GeometryIndices.install ops error).op10 square=ok doubled ∧ doubled.val<2147483647 ∧
      (NEB_GeometryIndices.install ops error).op7=ok one ∧ one.val<2147483647 ∧
      (NEB_GeometryIndices.install ops error).op8 doubled one=ok r.lineZ ∧ r.lineZ.val<2147483647 ∧
      (∀ x ∈ r.words, x≠0#u32) ∧
      flatOut.val=flat.val++r.words ∧ zsOut.val=zs.val++[r.lineZ] := by
  obtain ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,fields⟩ :=
    Port4C_GeometryGather.step (NEB_GeometryIndices.install ops error) start
      iter iter1 iterOut query zs zsOut flat flatOut next run
  rcases fields with ⟨it,cast,new,pointRun,division,leftEq,newLeft,lineX,rightEq,newRight,lineY,hx,hy,mul,dbl,unit,sub,raw,append,zsEq⟩
  have fi := NEB_GeometryIndices.accepted error u fibre new
  have fl := NEB_GeometryIndices.accepted error left fleft newLeft
  have fr := NEB_GeometryIndices.accepted error right fright newRight
  have leaves := NEB_GeometryIndices.primitives ops error
  have cp := leaves.point _ _ pointRun
  have cx := leaves.line _ _ lineX
  have cy := leaves.line _ _ lineY
  have cs := leaves.multiply _ _ _ cx cx mul
  have cd := leaves.double _ _ cs dbl
  have co := leaves.one _ unit
  have cz := leaves.subtract _ _ _ cd co sub
  exact ⟨r,u,parent,left,right,fibre,fleft,fright,point,square,doubled,one,
    it,cast,new,fi.1,fi.2,pointRun,cp.1,cp.2,division,leftEq,newLeft,fl.1,fl.2,lineX,cx,
    rightEq,newRight,fr.1,fr.2,lineY,cy,hx,hy,mul,cs,dbl,cd,unit,co,sub,cz,raw,append,zsEq⟩

theorem traversal {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32)
    (out : verifier.QueryGeometry) (fuel : Nat)
    (remaining : iter.i+fuel=iter.slice.val.length)
    (canonical : ∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x)
    (raw : ∀ x ∈ flat.val, x≠0#u32)
    (run : verifier.QueryGeometry.for_range_loop0
      (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
      iter start zs flat=ok (.Ok out)) :
    ∃ zsFinal flatFinal terminal,
      (∀ x ∈ flatFinal.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flatFinal.val, x≠0#u32) ∧
      verifier.QueryGeometry.for_range_loop0.body
        (Port4C_GeometryStd.install (NEB_GeometryIndices.install ops error))
        start terminal zsFinal flatFinal=ok (done (.Ok out)) ∧
      terminal.i=terminal.slice.val.length ∧
      zsFinal.val.length=zs.val.length+fuel ∧ flatFinal.val.length=flat.val.length+5*fuel :=
  Port5Q1_GeometryCanonical.traversal _ (NEB_GeometryIndices.primitives ops error)
    start iter zs flat out fuel remaining canonical raw run

#print axioms step
#print axioms traversal
end NEB_GeometryGatherDomains
end

```

Printed axioms (exit 0):

- `'NEB_GeometryGatherDomains.step' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryGatherDomains.traversal' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_GeometryModel (L043)

```lean
import NEB_GeometryGatherDomains
import Port5Q1_Geometry
set_option autoImplicit false
noncomputable section
namespace NEB_GeometryModel
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open Port3_NativeGeometryBody

def install {CoreError : Type} (ops : Ops CoreError) (error : CoreError) : Ops CoreError :=
  {NEB_GeometryIndices.install ops error with op11:=Port4C_InverseExecution.inverse_owned}

theorem primitives {CoreError : Type} (ops : Ops CoreError) (error : CoreError) :
    Port5Q1_GeometryCanonical.SessionAPrimitives (install ops error) := by
  have p := NEB_GeometryIndices.primitives ops error
  exact ⟨p.point,p.line,p.multiply,p.double,p.one,p.subtract⟩

/-- All inner canonical primitive predicates and the chosen inverse operation
are instantiated. The premise is the SAME adopted model parent success, not
an additional prefix/inverse/collect success premise or a native claim. -/
theorem for_range {CoreError : Type} (ops : Ops CoreError) (error : CoreError)
    (queries : Array U32 22#usize) (start end1 : Usize) (out : verifier.QueryGeometry)
    (nonempty : start.val<end1.val)
    (accepted : Port3_GeometryStage.geometry
      (Port5Q1_GeometryTerminal.install (install ops error)) queries start end1=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=end1.val-start.val ∧
      flat.val.length=5*(end1.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (end1.val-start.val)).map (Port4C_CollectLoop.record inverse) :=
  Port5Q1_Geometry.for_range (install ops error) (primitives ops error) rfl rfl rfl
    queries start end1 out nonempty accepted

#print axioms primitives
#print axioms for_range
end NEB_GeometryModel
end

```

Printed axioms (exit 0):

- `'NEB_GeometryModel.primitives' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryModel.for_range' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_SquareDomains (L044)

```lean
import NBG_SquareTrace
import NEB_PureFrame
set_option autoImplicit false
noncomputable section
namespace NEB_SquareDomains
open Aeneas Aeneas.Std Result AspisR1

theorem preserve {n : Nat} {before after : U32}
    (trace : NBG_SquareTrace.Trace n before after) (canonical : before.val<2147483647) :
    after.val<2147483647 := by
  induction trace with
  | done value => exact canonical
  | @step n before middle after cell tail ih =>
    have cm : middle.val<2147483647 := by rw [cell];exact Nat.mod_lt _ (by decide)
    exact ih cm

theorem positive {n : Nat} {before after : U32}
    (trace : NBG_SquareTrace.Trace n before after) (nonempty : 0<n) :
    after.val<2147483647 := by
  cases trace with
  | done value => omega
  | step cell tail =>
    apply preserve tail
    rw [cell]
    exact Nat.mod_lt _ (by decide)

theorem trace_exists (n : Nat) (before : U32) :
    ∃ after, NBG_SquareTrace.Trace n before after := by
  induction n generalizing before with
  | zero => exact ⟨before,.done before⟩
  | succ n ih =>
    obtain ⟨middle,run,value,_⟩ := LPf_BaseMultiply.source before before
    obtain ⟨after,tail⟩ := ih middle
    exact ⟨after,.step value tail⟩

/-- All raw initial words are allowed. Canonicality is derived after a positive
number of iterations, never imposed on the zero-iteration return. -/
theorem source (before : U32) (count : Usize) :
    ∃ after, AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count=ok after ∧
      NBG_SquareTrace.Trace count.val before after ∧
      (0<count.val → after.val<2147483647) := by
  obtain ⟨after,trace⟩ := trace_exists count.val before
  exact ⟨after,NBG_SquareTrace.native_result count before after trace,trace,positive trace⟩

#print axioms preserve
#print axioms positive
#print axioms trace_exists
#print axioms source
end NEB_SquareDomains
end

```

Printed axioms (exit 0):

- `'NEB_SquareDomains.preserve' does not depend on any axioms`.
- `'NEB_SquareDomains.positive' depends on axioms: [propext, Quot.sound]`.
- `'NEB_SquareDomains.trace_exists' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_SquareDomains.source' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_InverseCalls (L046)

```lean
import NEB_SquareDomains
import NBG_InverseBridge
set_option autoImplicit false
noncomputable section
namespace NEB_InverseCalls
open Aeneas Aeneas.Std Result AspisR1

/-- The actual seventeen-call DAG; no canonical input assumption or inner
callee domain/interpretation hypothesis is added. Zero is handled separately. -/
theorem nonzero (x : U32) (nonzero : x != 0#u32) :
    ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
      FIo_Native.aspis_core.field.M31.mul x x=ok m ∧ m.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m x=ok t2 ∧ t2.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t2 2#usize=ok m1 ∧ m1.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m1 t2=ok t4 ∧ t4.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t4 4#usize=ok m2 ∧ m2.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m2 t4=ok t8 ∧ t8.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t8 8#usize=ok m3 ∧ m3.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m3 t8=ok t16 ∧ t16.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t16 8#usize=ok m4 ∧ m4.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m4 t8=ok t24 ∧ t24.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t24 4#usize=ok m5 ∧ m5.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m5 t4=ok t28 ∧ t28.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t28 t28=ok m6 ∧ m6.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m6 x=ok t29 ∧ t29.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t29 t29=ok t30 ∧ t30.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t30 t30=ok m7 ∧ m7.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m7 x=ok out ∧ out.val<2147483647 ∧
      AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x=ok out := by
  obtain ⟨m,h_m,_,c_m⟩ := LPf_BaseMultiply.source x x
  obtain ⟨t2,h_t2,_,c_t2⟩ := LPf_BaseMultiply.source m x
  obtain ⟨m1,h_m1,_,c_m10⟩ := NEB_SquareDomains.source t2 2#usize
  have c_m1 : m1.val<2147483647 := c_m10 (by decide)
  obtain ⟨t4,h_t4,_,c_t4⟩ := LPf_BaseMultiply.source m1 t2
  obtain ⟨m2,h_m2,_,c_m20⟩ := NEB_SquareDomains.source t4 4#usize
  have c_m2 : m2.val<2147483647 := c_m20 (by decide)
  obtain ⟨t8,h_t8,_,c_t8⟩ := LPf_BaseMultiply.source m2 t4
  obtain ⟨m3,h_m3,_,c_m30⟩ := NEB_SquareDomains.source t8 8#usize
  have c_m3 : m3.val<2147483647 := c_m30 (by decide)
  obtain ⟨t16,h_t16,_,c_t16⟩ := LPf_BaseMultiply.source m3 t8
  obtain ⟨m4,h_m4,_,c_m40⟩ := NEB_SquareDomains.source t16 8#usize
  have c_m4 : m4.val<2147483647 := c_m40 (by decide)
  obtain ⟨t24,h_t24,_,c_t24⟩ := LPf_BaseMultiply.source m4 t8
  obtain ⟨m5,h_m5,_,c_m50⟩ := NEB_SquareDomains.source t24 4#usize
  have c_m5 : m5.val<2147483647 := c_m50 (by decide)
  obtain ⟨t28,h_t28,_,c_t28⟩ := LPf_BaseMultiply.source m5 t4
  obtain ⟨m6,h_m6,_,c_m6⟩ := LPf_BaseMultiply.source t28 t28
  obtain ⟨t29,h_t29,_,c_t29⟩ := LPf_BaseMultiply.source m6 x
  obtain ⟨t30,h_t30,_,c_t30⟩ := LPf_BaseMultiply.source t29 t29
  obtain ⟨m7,h_m7,_,c_m7⟩ := LPf_BaseMultiply.source t30 t30
  obtain ⟨out,h_out,_,c_out⟩ := LPf_BaseMultiply.source m7 x
  refine ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,h_m,c_m,h_t2,c_t2,h_m1,c_m1,h_t4,c_t4,h_m2,c_m2,h_t8,c_t8,h_m3,c_m3,h_t16,c_t16,h_m4,c_m4,h_t24,c_t24,h_m5,c_m5,h_t28,c_t28,h_m6,c_m6,h_t29,c_t29,h_t30,c_t30,h_m7,c_m7,h_out,c_out,?_⟩
  simp only [AspisR1M31Inverse.field.M31.inv,nonzero,bind_tc_ok,
    h_m,h_t2,h_m1,h_t4,h_m2,h_t8,h_m3,h_t16,h_m4,h_t24,h_m5,h_t28,h_m6,h_t29,h_t30,h_m7,h_out]
  simp [massert]

theorem zero : AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul 0#u32 =
    Port4C_InverseExecution.inverse_owned 0#u32 := NBG_InverseBridge.inverse_result _

#print axioms nonzero
#print axioms zero
end NEB_InverseCalls
end

```

Printed axioms (exit 0):

- `'NEB_InverseCalls.nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_InverseCalls.zero' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_WideRepresentation (L048)

```lean
import NEB_ArrayRefs
import NEB_PureFrame
import NBG_Embedding
set_option autoImplicit false
noncomputable section
namespace NEB_WideRepresentation
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs
abbrev EQ := AspisS1M31Embedding.aspis_core.field.QM31
abbrev EE := AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact

def into (x : NQ) : EQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def normalized (x : NQ) : NQ :=
  ⟨⟨AspisS1M31Embedding.Total.reduce x.c0.a,AspisS1M31Embedding.Total.reduce x.c0.b⟩,
   ⟨AspisS1M31Embedding.Total.reduce x.c1.a,AspisS1M31Embedding.Total.reduce x.c1.b⟩⟩
def embedded (x : NQ) : EE :=
  ⟨into (normalized x),⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

theorem word (x : U32) :
    NEB_AdditiveRef.normalize_word x=ok (AspisS1M31Embedding.Total.reduce x) := by
  rw [NEB_WordRefs.normalize]
  simpa only [AspisS1M31Embedding.aspis_core.field.P] using AspisS1M31Embedding.Total.rem_total x

theorem canonical (x : NQ) : canonQ (normalized x) := by
  have c (w : U32) : (AspisS1M31Embedding.Total.reduce w).val<2147483647 := by
    rw [AspisS1M31Embedding.Total.reduce_val]
    exact Nat.mod_lt _ (by decide)
  exact ⟨⟨c _,c _⟩,⟨c _,c _⟩⟩

/-- Same raw input words and exact full record across the two emitted carriers. -/
theorem canonical_calls (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31 (into x)=
      ok (into (normalized x)) ∧
    NEB_AdditiveRef.normalize_word x.c0.a=ok (normalized x).c0.a ∧
    NEB_AdditiveRef.normalize_word x.c0.b=ok (normalized x).c0.b ∧
    NEB_AdditiveRef.normalize_word x.c1.a=ok (normalized x).c1.a ∧
    NEB_AdditiveRef.normalize_word x.c1.b=ok (normalized x).c1.b := by
  have r (w : U32) : w%2147483647#u32=ok (AspisS1M31Embedding.Total.reduce w) := by
    simpa only [AspisS1M31Embedding.aspis_core.field.P] using AspisS1M31Embedding.Total.rem_total w
  refine ⟨?_,?_,word _,word _,word _,word _⟩
  · simp only [FIo_Native.aspis_core.field.wide_exact.canonical_qm31,
      FIo_Native.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      FIo_Native.aspis_core.field.P,r,bind_tc_ok,normalized]
  · simp only [AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31,
      AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      AspisS1M31Embedding.aspis_core.field.P,into,r,bind_tc_ok,normalized]

theorem canonical_frame {S Event : Type} (state : S) (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    canonQ (normalized x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x)=ok (normalized x,state,[]) :=
  ⟨(canonical_calls x).1,canonical x,NEB_PureFrame.successful state _ _ (canonical_calls x).1⟩

theorem embedding_call (x : NQ) :
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) := by
  simpa only [into,embedded,normalized] using NBG_Embedding.from_qm31_result (into x)

theorem embedding_frame {S Event : Type} (state : S) (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    canonQ (normalized x) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x))=
        ok (embedded x,state,[]) :=
  ⟨(canonical_calls x).1,canonical x,embedding_call x,
    NEB_PureFrame.successful state _ _ (embedding_call x)⟩

theorem limbs_frame {S Event : Type} (state : S) (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x=ok (wordsE x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x)=ok (wordsE x,state,[]) :=
  ⟨rfl,NEB_PureFrame.successful state _ _ rfl⟩

#print axioms word
#print axioms canonical
#print axioms canonical_calls
#print axioms canonical_frame
#print axioms embedding_call
#print axioms embedding_frame
#print axioms limbs_frame
end NEB_WideRepresentation
end

```

Printed axioms (exit 0):

- `'NEB_WideRepresentation.word' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_WideRepresentation.canonical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_WideRepresentation.canonical_calls' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_WideRepresentation.canonical_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_WideRepresentation.embedding_call' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_WideRepresentation.embedding_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_WideRepresentation.limbs_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_RepresentationRefs (L052)

```lean
import NEB_RepresentationRef.Funs
import NEB_WideRepresentation
set_option autoImplicit false
noncomputable section
namespace NEB_RepresentationRefs
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs NEB_WideRepresentation

def c (x : NC) : NEB_RepresentationRef.C := ⟨x.a,x.b⟩
def q (x : NQ) : NEB_RepresentationRef.Q := ⟨c x.c0,c x.c1⟩
def e (x : NE) : NEB_RepresentationRef.E := ⟨q x.c0,q x.c1⟩
def backQ (x : NEB_RepresentationRef.Q) : NQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def backE (x : NEB_RepresentationRef.E) : NE := ⟨backQ x.c0,backQ x.c1⟩
def embeddingE (x : EE) : NEB_RepresentationRef.E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def backEmbedding (x : NEB_RepresentationRef.E) : EE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem q_roundtrip (x : NQ) : backQ (q x)=x := rfl
theorem e_roundtrip (x : NE) : backE (e x)=x := rfl
theorem embedding_roundtrip (x : EE) : backEmbedding (embeddingE x)=x := rfl

theorem q_injective : Function.Injective q := by
  intro x y h
  exact (q_roundtrip x).symm.trans ((congrArg backQ h).trans (q_roundtrip y))
theorem e_injective : Function.Injective e := by
  intro x y h
  exact (e_roundtrip x).symm.trans ((congrArg backE h).trans (e_roundtrip y))
theorem embedding_injective : Function.Injective embeddingE := by
  intro x y h
  exact (embedding_roundtrip x).symm.trans ((congrArg backEmbedding h).trans (embedding_roundtrip y))

/-- Independent record reference: all four words, arbitrary raw inputs. -/
theorem canonical (x : NQ) :
    NEB_RepresentationRef.canonical (q x)=ok (q (normalized x)) := by
  have rem (w : U32) : w%2147483647#u32=ok (AspisS1M31Embedding.Total.reduce w) := by
    simpa only [AspisS1M31Embedding.aspis_core.field.P] using AspisS1M31Embedding.Total.rem_total w
  simp only [NEB_RepresentationRef.canonical,NEB_RepresentationRef.P,q,c,
    rem,bind_tc_ok,normalized]

theorem embedding (x : NQ) :
    NEB_RepresentationRef.embed (q x)=ok (embeddingE (embedded x)) := by
  unfold NEB_RepresentationRef.embed
  rw [canonical x]
  rfl

theorem getter (x : NE) :
    NEB_RepresentationRef.words (e x)=FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x := rfl

theorem canonical_frame {S Event : Type} (state : S) (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    NEB_RepresentationRef.canonical (q x)=ok (q (normalized x)) ∧ canonQ (normalized x) ∧
    NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x)=
      ok (normalized x,state,[]) ∧
    NEB_PureFrame.run (Event:=Event) state (NEB_RepresentationRef.canonical (q x))=
      ok (q (normalized x),state,[]) :=
  ⟨(canonical_calls x).1,canonical x,NEB_WideRepresentation.canonical x,
    NEB_PureFrame.successful state _ _ (canonical_calls x).1,
    NEB_PureFrame.successful state _ _ (canonical x)⟩

theorem embedding_frame {S Event : Type} (state : S) (x : NQ) :
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) ∧
    NEB_RepresentationRef.embed (q x)=ok (embeddingE (embedded x)) ∧
    canonQ (normalized x) ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x))=ok (embedded x,state,[]) ∧
    NEB_PureFrame.run (Event:=Event) state (NEB_RepresentationRef.embed (q x))=
      ok (embeddingE (embedded x),state,[]) :=
  ⟨embedding_call x,embedding x,NEB_WideRepresentation.canonical x,
    NEB_PureFrame.successful state _ _ (embedding_call x),
    NEB_PureFrame.successful state _ _ (embedding x)⟩

theorem getter_frame {S Event : Type} (state : S) (x : NE) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x=ok (wordsE x) ∧
    NEB_RepresentationRef.words (e x)=ok (wordsE x) ∧
    NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x)=
      ok (wordsE x,state,[]) ∧
    NEB_PureFrame.run (Event:=Event) state (NEB_RepresentationRef.words (e x))=ok (wordsE x,state,[]) :=
  ⟨rfl,getter x,NEB_PureFrame.successful state _ _ rfl,NEB_PureFrame.successful state _ _ (getter x)⟩

#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms embedding_roundtrip
#print axioms q_injective
#print axioms e_injective
#print axioms embedding_injective
#print axioms canonical
#print axioms embedding
#print axioms getter
#print axioms canonical_frame
#print axioms embedding_frame
#print axioms getter_frame
end NEB_RepresentationRefs
end

```

Printed axioms (exit 0):

- `'NEB_RepresentationRefs.q_roundtrip' does not depend on any axioms`.
- `'NEB_RepresentationRefs.e_roundtrip' does not depend on any axioms`.
- `'NEB_RepresentationRefs.embedding_roundtrip' does not depend on any axioms`.
- `'NEB_RepresentationRefs.q_injective' does not depend on any axioms`.
- `'NEB_RepresentationRefs.e_injective' does not depend on any axioms`.
- `'NEB_RepresentationRefs.embedding_injective' does not depend on any axioms`.
- `'NEB_RepresentationRefs.canonical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_RepresentationRefs.embedding' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_RepresentationRefs.getter' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_RepresentationRefs.canonical_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_RepresentationRefs.embedding_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_RepresentationRefs.getter_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_EmbeddingDomain (L054)

```lean
import NEB_RepresentationRefs
set_option autoImplicit false
noncomputable section
namespace NEB_EmbeddingDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_WideRepresentation

def Canonical (x : EE) : Prop :=
  ((x.c0.c0.a.val<2147483647 ∧ x.c0.c0.b.val<2147483647) ∧
   (x.c0.c1.a.val<2147483647 ∧ x.c0.c1.b.val<2147483647)) ∧
  ((x.c1.c0.a.val<2147483647 ∧ x.c1.c0.b.val<2147483647) ∧
   (x.c1.c1.a.val<2147483647 ∧ x.c1.c1.b.val<2147483647))

theorem canonical_output (x : NQ) : Canonical (embedded x) := by
  have c := NEB_WideRepresentation.canonical x
  have zero : (0#u32).val<2147483647 := by decide
  exact ⟨c,⟨⟨zero,zero⟩,⟨zero,zero⟩⟩⟩

/-- Callee selected PacketDomain is every raw four-limb word. Its exact
emitted carrier and the returned canonical carrier are derived at this call. -/
theorem canonical_edge (x : NQ) :
    FIo_Native.aspis_core.field.wide_exact.canonical_qm31 x=ok (normalized x) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.canonical_qm31 (into x)=
      ok (into (normalized x)) ∧
    NEB_RepresentationRef.canonical (NEB_RepresentationRefs.q x)=
      ok (NEB_RepresentationRefs.q (normalized x)) ∧
    AspisS1M31Embedding.aspis_core.field.wide_exact.WideExact.from_qm31 (into x)=ok (embedded x) ∧
    Canonical (embedded x) :=
  ⟨(canonical_calls x).1,(canonical_calls x).2.1,NEB_RepresentationRefs.canonical x,
    embedding_call x,canonical_output x⟩

#print axioms canonical_output
#print axioms canonical_edge
end NEB_EmbeddingDomain
end

```

Printed axioms (exit 0):

- `'NEB_EmbeddingDomain.canonical_output' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_EmbeddingDomain.canonical_edge' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_MulReducerCall (L056)

```lean
import NEB_ReducerCall
import NBG_InverseBridge
import JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
namespace NEB_MulReducerCall
open Aeneas Aeneas.Std Result AspisR1

def product (x y : U32) : U64 :=
  U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)

theorem domain (x y : U32) : NEB_ReducerCall.PacketDomain (product x y) :=
  NEB_ReducerCall.all_domain _

theorem input_value (x y : U32) : (product x y).val=x.val*y.val :=
  LPf_BaseMultiply.word_product x y

/-- Actual translated caller body, same input to the private reducer, and
same scalar reply. No canonical operand assumption is introduced. -/
theorem callsite (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y=
      FIo_Native.aspis_core.field.reduce_u64 (product x y) := by
  simp only [FIo_Native.aspis_core.field.M31.mul,product,lift,bind_tc_ok]
  change (do let z ← FIo_Native.aspis_core.field.reduce_u64 (product x y); ok z)=
    FIo_Native.aspis_core.field.reduce_u64 (product x y)
  generalize hr : FIo_Native.aspis_core.field.reduce_u64 (product x y)=r
  cases r <;> rfl

theorem value (x y : U32) : ∃ z,
    FIo_Native.aspis_core.field.M31.mul x y=ok z ∧
    FIo_Native.aspis_core.field.reduce_u64 (product x y)=ok z ∧
    z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,v,cz⟩ := LPf_CoreReduction.source (product x y)
  exact ⟨z,(callsite x y).trans run,run,by rw [input_value] at v;exact v,cz⟩

theorem state_effects {S Event : Type} (state : S) (x y : U32) : ∃ z,
    NEB_ReducerCall.withState (Event:=Event) state
      (FIo_Native.aspis_core.field.M31.mul x y)=ok (z,state,[]) ∧
    NEB_ReducerCall.withState (Event:=Event) state
      (FIo_Native.aspis_core.field.reduce_u64 (product x y))=ok (z,state,[]) ∧
    z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
  obtain ⟨z,run,reducer,v,cz⟩ := value x y
  exact ⟨z,by simp only [NEB_ReducerCall.withState,run,bind_tc_ok],
    by simp only [NEB_ReducerCall.withState,reducer,bind_tc_ok],v,cz⟩

#print axioms domain
#print axioms input_value
#print axioms callsite
#print axioms value
#print axioms state_effects
#print axioms NBG_InverseBridge.mul_eq_probe
#print axioms AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.generated_m31_mul_eq_probe
end NEB_MulReducerCall

```

Printed axioms (exit 0):

- `'NEB_MulReducerCall.domain' depends on axioms: [propext, Quot.sound]`.
- `'NEB_MulReducerCall.input_value' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_MulReducerCall.callsite' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_MulReducerCall.value' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_MulReducerCall.state_effects' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NBG_InverseBridge.mul_eq_probe' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.generated_m31_mul_eq_probe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]`.

### NEB_FieldFrames (L057)

```lean
import NEB_CMCalls
import NEB_QMCalls
import NEB_WideCalls
import NEB_ByRCalls
import NEB_PureFrame
set_option autoImplicit false
namespace NEB_FieldFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem cm_mul {S Event : Type} (state : S) (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y=ok z ∧ canonC z ∧
      cw z=mulC (cw x) (cw y) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.mul x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_FieldValues.cm_mul x y hx hy
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem qm_mul {S Event : Type} (state : S) (x y : NQ) (hx : canonQ x) (hy : canonQ y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y=ok z ∧ canonQ z ∧
      qw z=mulQ (qw x) (qw y) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.mul x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.qm_mul x y hx hy
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem wide_mul {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y=ok z ∧ canonE z ∧
      ew z=mulE (ew x) (ew y) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.wide_mul x y hx hy
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem by_r {S Event : Type} (state : S) (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x=ok z ∧ canonC z ∧
      cw z=byR (cw x) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.mul_by_r x)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_FieldValues.by_r x hx
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem mul_u {S Event : Type} (state : S) (x : NQ) (hx : canonQ x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.mul_u x=ok z ∧ canonQ z ∧
      qw z=mulU (qw x) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.mul_u x)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_TowerValues.mul_u x hx
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem cm_scale {S Event : Type} (state : S) (x : NC) (scalar : U32) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul_m31 x scalar=ok z ∧ canonC z ∧
      cw z=((x.a.val*scalar.val)%2147483647,(x.b.val*scalar.val)%2147483647) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.CM31.mul_m31 x scalar)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_MixedValues.cm_m31 x scalar
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem qm_scale {S Event : Type} (state : S) (x : NQ) (scalar : U32) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul_m31 x scalar=ok z ∧ canonQ z ∧
      qw z=(((x.c0.a.val*scalar.val)%2147483647,(x.c0.b.val*scalar.val)%2147483647),((x.c1.a.val*scalar.val)%2147483647,(x.c1.b.val*scalar.val)%2147483647)) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.QM31.mul_m31 x scalar)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := LPi_MixedValues.qm_m31 x scalar
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem wide_scale {S Event : Type} (state : S) (x : NE) (scalar : U32) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x scalar=ok z ∧ canonE z ∧
      ew z=(NBG_FieldDischarge.scaleQ (qw x.c0) (scalar.val%2147483647),NBG_FieldDischarge.scaleQ (qw x.c1) (scalar.val%2147483647)) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x scalar)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := NBG_FieldDischarge.wide_scale x scalar
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩

/-- Existing translated field bridge, with exact value and empty pure frame. -/
theorem wide_mixed {S Event : Type} (state : S) (x : NE) (y : NQ) (hx : canonE x) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y=ok z ∧ canonE z ∧
      ew z=(mulQ (qw x.c0) (NBG_FieldDischarge.modQ (qw y)),mulQ (qw x.c1) (NBG_FieldDischarge.modQ (qw y))) ∧
      NEB_PureFrame.run (Event:=Event) state (FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y)=ok (z,state,[]) := by
  obtain ⟨z,run,canonical,value⟩ := NBG_FieldDischarge.wide_qm x y hx
  exact ⟨z,run,canonical,value,NEB_PureFrame.successful state _ _ run⟩
#print axioms cm_mul
#print axioms qm_mul
#print axioms wide_mul
#print axioms by_r
#print axioms mul_u
#print axioms cm_scale
#print axioms qm_scale
#print axioms wide_scale
#print axioms wide_mixed
end NEB_FieldFrames

```

Printed axioms (exit 0):

- `'NEB_FieldFrames.cm_mul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.qm_mul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.wide_mul' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.by_r' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.mul_u' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.cm_scale' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.qm_scale' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.wide_scale' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_FieldFrames.wide_mixed' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_CMCarrier (L058)

```lean
import NEB_CMCalls
set_option autoImplicit false
namespace NEB_CMCarrier
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem lossless (x : U32) :
    (core.convert.num.FromU64U32.from x).val=x.val := by scalar_tac

/-- The four actual u64::from arguments in the frozen complex product body. -/
theorem actual_casts (x y : NC) :
    (core.convert.num.FromU64U32.from x.a).val=x.a.val ∧
    (core.convert.num.FromU64U32.from x.b).val=x.b.val ∧
    (core.convert.num.FromU64U32.from y.a).val=y.a.val ∧
    (core.convert.num.FromU64U32.from y.b).val=y.b.val :=
  ⟨lossless _,lossless _,lossless _,lossless _⟩

#print axioms lossless
#print axioms actual_casts
end NEB_CMCarrier

```

Printed axioms (exit 0):

- `'NEB_CMCarrier.lossless' depends on axioms: [propext, Quot.sound]`.
- `'NEB_CMCarrier.actual_casts' depends on axioms: [propext, Quot.sound]`.

### NEB_NativeFieldScalars (L060)

```lean
import NEB_MulReducerCall
import NEB_CMCarrier
import FIo_ScalarBridge
set_option autoImplicit false
namespace NEB_NativeFieldScalars
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem size64 : UScalar.size .U64=18446744073709551616 := by
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]

theorem m31_checked_product (x y : U32) :
    (UScalar.cast .U64 x)*(UScalar.cast .U64 y)=ok (NEB_MulReducerCall.product x y) := by
  apply FIo_ScalarBridge.mul
  have xv : (UScalar.cast .U64 x).val=x.val := by scalar_tac
  have yv : (UScalar.cast .U64 y).val=y.val := by scalar_tac
  rw [xv,yv,size64]
  exact LPf_BaseMultiply.product_bound x y

theorem sum_checked (x : NC) :
    (core.convert.num.FromU64U32.from x.a)+(core.convert.num.FromU64U32.from x.b)=
      ok (LPi_CMProduct.sum x) := by
  apply FIo_ScalarBridge.add
  rw [NEB_CMCarrier.lossless,NEB_CMCarrier.lossless,size64]
  have a : x.a.val<4294967296 := by scalar_tac
  have b : x.b.val<4294967296 := by scalar_tac
  change x.a.val+x.b.val<18446744073709551616
  omega

/-- This is the checked scalar expression in the ACTUAL frozen caller; its
sums and product equal the emitted raw recurrence input without overflow. -/
theorem cross_checked (x y : NC) (hx : canonC x) (hy : canonC y) :
    (do
      let a ← (core.convert.num.FromU64U32.from x.a)+(core.convert.num.FromU64U32.from x.b)
      let b ← (core.convert.num.FromU64U32.from y.a)+(core.convert.num.FromU64U32.from y.b)
      a*b)=ok (LPi_CMProduct.cross x y) := by
  rw [sum_checked x,sum_checked y]
  simp only [bind_tc_ok]
  apply FIo_ScalarBridge.mul
  rw [LPi_CMProduct.sum_value,LPi_CMProduct.sum_value,size64]
  have a : x.a.val+x.b.val<4294967296 := by rcases hx with ⟨_,_⟩;omega
  have b : y.a.val+y.b.val<4294967296 := by rcases hy with ⟨_,_⟩;omega
  exact Nat.mul_lt_mul_of_lt_of_lt a b

#print axioms size64
#print axioms m31_checked_product
#print axioms sum_checked
#print axioms cross_checked
end NEB_NativeFieldScalars

```

Printed axioms (exit 0):

- `'NEB_NativeFieldScalars.size64' depends on axioms: [propext]`.
- `'NEB_NativeFieldScalars.m31_checked_product' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_NativeFieldScalars.sum_checked' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_NativeFieldScalars.cross_checked' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_TableCalls (L062)

```lean
import NEB_PointCalls
import NBG_Constructors
import NEB_PureFrame
import NDH_Geometry
import R17CurrentCM31Semantics
set_option autoImplicit false
namespace NEB_TableCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

def fromPublic (x : AspisR1PublicPreparation.aspis_core.field.CM31) : field.CM31 := ⟨x.a,x.b⟩

/-- Actual emitted constructor, both full raw words, and the exact table-call
carrier. No canonicality or successful-child premise is introduced. -/
theorem constructor (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b=ok ⟨a,b⟩ ∧
    NEA_FieldProduct.ops.new a b=ok ⟨a,b⟩ ∧
    (do let x ← AspisR1PublicPreparation.aspis_core.field.CM31.new a b
        ok (fromPublic x))=NEA_FieldProduct.ops.new a b := by
  exact ⟨NBG_Constructors.cm31_new a b,rfl,by rw [NBG_Constructors.cm31_new];rfl⟩

theorem table_body (a b : U32) :
    fast_domain.table_value NEA_FieldProduct.ops (a,b)=NEA_FieldProduct.ops.new a b ∧
    fast_domain.table_value NEA_FieldProduct.ops (a,b)=ok ⟨a,b⟩ := ⟨rfl,rfl⟩

/-- The selected old table packet's dictionary and the point packet's emitted
field dictionary agree on this ACTUAL constructor call; multiplication unused. -/
theorem selected_table (v : U32 × U32) :
    (do let w ← NDH_Reference.table_ref v;ok (field.CM31.mk w.1 w.2))=
      fast_domain.table_value R17CurrentCM31Semantics.operations v ∧
    fast_domain.table_value R17CurrentCM31Semantics.operations v=
      fast_domain.table_value NEA_FieldProduct.ops v := by
  rcases v with ⟨a,b⟩
  exact ⟨NDH_Geometry.table _ (fun _ _ => rfl) _,rfl⟩

theorem constructor_frame {S Event : Type} (state : S) (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b=ok ⟨a,b⟩ ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisR1PublicPreparation.aspis_core.field.CM31.new a b)=ok (⟨a,b⟩,state,[]) :=
  ⟨NBG_Constructors.cm31_new a b,NEB_PureFrame.successful state _ _ (NBG_Constructors.cm31_new a b)⟩

theorem table_frame {S Event : Type} (state : S) (v : U32 × U32) :
    fast_domain.table_value R17CurrentCM31Semantics.operations v=ok ⟨v.1,v.2⟩ ∧
    fast_domain.table_value NEA_FieldProduct.ops v=ok ⟨v.1,v.2⟩ ∧
    NDH_Reference.table_ref v=ok v ∧
    NEB_PureFrame.run (Event:=Event) state
      (fast_domain.table_value NEA_FieldProduct.ops v)=ok (⟨v.1,v.2⟩,state,[]) := by
  cases v with
  | mk a b => exact ⟨rfl,rfl,rfl,NEB_PureFrame.successful state _ _ rfl⟩

theorem getter_frame {S Event : Type} (state : S) (u : Usize) (admitted : u.val<262144) :
    domain.FibreIndex.get u=ok u ∧ NDH_Reference.fibre_get_ref u=ok u ∧
    NEB_PureFrame.run (Event:=Event) state (domain.FibreIndex.get u)=ok (u,state,[]) :=
  ⟨rfl,rfl,NEB_PureFrame.successful state _ _ rfl⟩

#print axioms constructor
#print axioms table_body
#print axioms selected_table
#print axioms constructor_frame
#print axioms table_frame
#print axioms getter_frame
end NEB_TableCalls

```

Printed axioms (exit 0):

- `'NEB_TableCalls.constructor' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_TableCalls.table_body' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_TableCalls.selected_table' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_TableCalls.constructor_frame' depends on axioms: [propext]`.
- `'NEB_TableCalls.table_frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_TableCalls.getter_frame' depends on axioms: [propext]`.

### NEB_GeometryFieldPorts (L063)

```lean
import NEB_TableCalls
import NEB_LineCalls
import NBG_InverseBridge
set_option autoImplicit false
namespace NEB_GeometryFieldPorts
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual LPi_FieldValues

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1Qm31ArithmeticProbe.field.M31.add x y := by
  obtain ⟨a,ha,va,_⟩ := LPi_NatBase.add x y hx hy
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1Qm31ArithmeticProbe.field.M31.sub x y := by
  obtain ⟨a,ha,va,_⟩ := LPi_NatBase.sub x y hx hy
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
  have same : a=b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

theorem double (x : U32) (hx : x.val<2147483647) :
    FIo_Native.aspis_core.field.M31.double x=AspisR1Qm31ArithmeticProbe.field.M31.double x := by
  exact add x x hx hx

/-- Instantiate the ACTUAL adopted geometry dictionary, not only a new emitted
field dictionary with similar field names. -/
theorem physical : NEA_PointComplete.PhysicalInterpretation R17CurrentCM31Semantics.operations := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro x y hx hy
  obtain ⟨z,run,cz,real,imag⟩ := ExtractedCurrentCM31Mul.current_mul_words
    (R17CurrentCM31Semantics.toArithmetic x) (R17CurrentCM31Semantics.toArithmetic y) hx hy
  refine ⟨R17CurrentCM31Semantics.fromArithmetic z,?_,cz,?_⟩
  · simp only [R17CurrentCM31Semantics.operations,run,bind_tc_ok]
  · apply Prod.ext
    · simpa only [R17CurrentCM31Semantics.fromArithmetic,R17CurrentCM31Semantics.toArithmetic,
        LPi_FieldValues.mulC,LPi_CMProduct.realWord,ExtractedCurrentCM31Mul.realWord] using real
    · simpa only [R17CurrentCM31Semantics.fromArithmetic,R17CurrentCM31Semantics.toArithmetic,
        LPi_FieldValues.mulC,LPi_CMProduct.imagWord,ExtractedCurrentCM31Mul.imagWord] using imag

theorem cm_eq (x y : field.CM31) (hx : NEA_FieldProduct.Canonical x) (hy : NEA_FieldProduct.Canonical y) :
    R17CurrentCM31Semantics.operations.mul x y=NEA_FieldProduct.ops.mul x y := by
  obtain ⟨a,ha,_,va⟩ := physical.multiply x y hx hy
  obtain ⟨b,hb,_,vb⟩ := NEA_PointComplete.emitted_interpretation.multiply x y hx hy
  have values : (a.a.val,a.b.val)=(b.a.val,b.b.val) := va.trans vb.symm
  have ae : a.a=b.a := UScalar.eq_of_val_eq (congrArg Prod.fst values)
  have be : a.b=b.b := UScalar.eq_of_val_eq (congrArg Prod.snd values)
  have same : a=b := by cases a;cases b;simp_all
  rw [ha,hb,same]

#print axioms add
#print axioms sub
#print axioms double
#print axioms physical
#print axioms cm_eq
#print axioms NBG_InverseBridge.mul_eq_probe
end NEB_GeometryFieldPorts

```

Printed axioms (exit 0):

- `'NEB_GeometryFieldPorts.add' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryFieldPorts.sub' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryFieldPorts.double' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryFieldPorts.physical' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryFieldPorts.cm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NBG_InverseBridge.mul_eq_probe' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_ActualGeometryPoint (L064)

```lean
import NEB_GeometryFieldPorts
set_option autoImplicit false
namespace NEB_ActualGeometryPoint
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

/-- The actual selected table reads establish both product domains; the
original deployed-cohort dictionary is used in the returned point equation. -/
theorem calls (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (iA iB : Usize) (a b : U32 × U32) (z : field.CM31),
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b ∧
      NEA_FieldProduct.Canonical ⟨a.1,a.2⟩ ∧ NEA_FieldProduct.Canonical ⟨b.1,b.2⟩ ∧
      NEA_FieldProduct.ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      R17CurrentCM31Semantics.operations.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z ∧
      NEA_FieldProduct.Canonical z ∧
      NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (NEA_PointBridge.record a b z) ∧
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,mul,cz,_⟩ :=
    NEB_PointCalls.selected_product u admitted
  have actual : R17CurrentCM31Semantics.operations.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z :=
    (NEB_GeometryFieldPorts.cm_eq _ _ ca cb).trans mul
  have selected := NEA_PointBridge.selected R17CurrentCM31Semantics.operations u iA iB a b z
    mask shift readA readB (fun _ _ => rfl) actual
  exact ⟨iA,iB,a,b,z,mask,shift,readA,readB,ca,cb,mul,actual,cz,selected.1,selected.2⟩

theorem frame {S Event : Type} (state : S) (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ point : domain.Point field.M31,
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      NEB_PureFrame.run (Event:=Event) state
        (fast_domain.fibre_point R17CurrentCM31Semantics.operations u)=ok (point,state,[]) := by
  obtain ⟨_,_,_,_,z,_,_,_,_,_,_,_,_,cz,_,run⟩ := calls u admitted
  exact ⟨⟨z.a,z.b⟩,run,cz.1,cz.2,NEB_PureFrame.successful state _ _ run⟩

#print axioms calls
#print axioms frame
end NEB_ActualGeometryPoint

```

Printed axioms (exit 0):

- `'NEB_ActualGeometryPoint.calls' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_ActualGeometryPoint.frame' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_GeometryDictionaryEq (L066)

```lean
import NEB_ActualGeometryPoint
set_option autoImplicit false
namespace NEB_GeometryDictionaryEq
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

theorem point (u : Usize) :
    fast_domain.fibre_point R17CurrentCM31Semantics.operations u=
      fast_domain.fibre_point NEA_FieldProduct.ops u := by
  unfold fast_domain.fibre_point
  simp only [domain.FibreIndex.get,lift,bind_tc_ok]
  generalize readA : Array.index_usize fast_domain.TABLE_A (u &&& 511#usize)=ra
  cases ra with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [bind_tc_ok]
    rw [show fast_domain.table_value R17CurrentCM31Semantics.operations a=ok ⟨a.1,a.2⟩ from by cases a;rfl,
        show fast_domain.table_value NEA_FieldProduct.ops a=ok ⟨a.1,a.2⟩ from by cases a;rfl]
    simp only [bind_tc_ok]
    generalize shift : u >>> 9#i32=shifted
    cases shifted with
    | fail e => rfl
    | div => rfl
    | ok iB =>
      simp only [bind_tc_ok]
      generalize readB : Array.index_usize fast_domain.TABLE_B iB=rb
      cases rb with
      | fail e => rfl
      | div => rfl
      | ok b =>
        simp only [bind_tc_ok]
        rw [show fast_domain.table_value R17CurrentCM31Semantics.operations b=ok ⟨b.1,b.2⟩ from by cases b;rfl,
            show fast_domain.table_value NEA_FieldProduct.ops b=ok ⟨b.1,b.2⟩ from by cases b;rfl]
        simp only [bind_tc_ok]
        have ca := NEA_TableCanonical.readA (u &&& 511#usize)
          (NEB_PointSuccess.read_bound _ _ _ readA) a readA
        have cb := NEA_TableCanonical.readB iB (NEB_PointSuccess.read_bound _ _ _ readB) b readB
        rw [NEB_GeometryFieldPorts.cm_eq ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb]

theorem line (u : Usize) :
    R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u=
      R17FibrePointLineNodeActual.line_node NEA_FieldProduct.ops R17CurrentM31Semantics.operations u := by
  unfold R17FibrePointLineNodeActual.line_node
  rw [point]

theorem point_success (u : Usize) (p : domain.Point field.M31)
    (run : fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok p) :
    p.x.val<2147483647 ∧ p.y.val<2147483647 := by
  rw [point] at run
  exact NEB_PointSuccess.canonical u p run

theorem line_success (u : Usize) (out : U32)
    (run : R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
      R17CurrentM31Semantics.operations u=ok out) : out.val<2147483647 := by
  rw [line] at run
  exact NEB_LineCalls.successful u out run

#print axioms point
#print axioms line
#print axioms point_success
#print axioms line_success
end NEB_GeometryDictionaryEq

```

Printed axioms (exit 0):

- `'NEB_GeometryDictionaryEq.point' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryDictionaryEq.line' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryDictionaryEq.point_success' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `'NEB_GeometryDictionaryEq.line_success' depends on axioms: [propext, Classical.choice, Quot.sound]`.

### NEB_ActualGeometryLine (L067)

```lean
import NEB_GeometryDictionaryEq
set_option autoImplicit false
namespace NEB_ActualGeometryLine
open Aeneas Aeneas.Std Result AspisR1 AspisR1QueryGeometryActual

theorem calls {S Event : Type} (state : S) (u : Usize) (admitted : NEA_PointBridge.PacketDomain u) :
    ∃ (point : domain.Point field.M31) (square doubled out : U32),
      fast_domain.fibre_point R17CurrentCM31Semantics.operations u=ok point ∧
      point.x.val<2147483647 ∧ point.y.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul point.x point.x=ok square ∧ square.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.double square=ok doubled ∧ doubled.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.sub doubled 1#u32=ok out ∧ out.val<2147483647 ∧
      NEA_Reference.line_double_sub_ref square=ok out ∧
      R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
        R17CurrentM31Semantics.operations u=ok out ∧
      NEB_PureFrame.run (Event:=Event) state
        (R17FibrePointLineNodeActual.line_node R17CurrentCM31Semantics.operations
          R17CurrentM31Semantics.operations u)=ok (out,state,[]) := by
  obtain ⟨p,square,out,point,cx,cy,product,value,reference,line,co⟩ :=
    NEA_LineComplete.cohort R17CurrentCM31Semantics.operations NEB_GeometryFieldPorts.physical u admitted
  obtain ⟨s,run,_,cs⟩ := ExtractedCurrentReducer.current_mul_mod p.x p.x
  have same : s=square := Result.ok.inj (run.symm.trans product)
  subst s
  have nativeProduct : FIo_Native.aspis_core.field.M31.mul p.x p.x=ok square :=
    (NBG_InverseBridge.mul_eq_probe _ _).trans product
  obtain ⟨d,add,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square cs cs
  have probeDouble : AspisR1Qm31ArithmeticProbe.field.M31.double square=ok d := by
    simpa only [AspisR1Qm31ArithmeticProbe.field.M31.double] using add
  have nativeDouble : FIo_Native.aspis_core.field.M31.double square=ok d :=
    (NEB_GeometryFieldPorts.double square cs).trans probeDouble
  have probeSub : AspisR1Qm31ArithmeticProbe.field.M31.sub d 1#u32=ok out := by
    rw [NEA_LineTail.reference square cs,probeDouble] at reference
    simpa only [bind_tc_ok] using reference
  have nativeSub : FIo_Native.aspis_core.field.M31.sub d 1#u32=ok out :=
    (NEB_GeometryFieldPorts.sub d 1#u32 cd (by decide)).trans probeSub
  exact ⟨p,square,d,out,point,cx,cy,nativeProduct,cs,nativeDouble,cd,nativeSub,co,
    reference,line,NEB_PureFrame.successful state _ _ line⟩

#print axioms calls
end NEB_ActualGeometryLine

```

Printed axioms (exit 0):

- `'NEB_ActualGeometryLine.calls' depends on axioms: [propext, Classical.choice, Quot.sound]`.
