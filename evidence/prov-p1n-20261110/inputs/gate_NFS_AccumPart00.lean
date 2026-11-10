import Lean
import NFN_PhaseTransport
import NEV_AccumulateRaw.Types
import NEV_CodeFieldRaw.Funs
import NEI_LineFull.Funs
import NEI_PushRaw.Funs
import RPz7_FIo_NativeFuns
import RPz7_S1M31EmbeddingTotalV1
import NBF_RowInstall
import NEV_AccumulateCarriers
import NEI_PushRawAssociation
import Port3_NativeRowFrame
import Aeneas
import NBF_BasisInstall
import NEG_FoldAssociation
import RPu_JFv_RawExtractedSemanticCallOpsV20

-- BEGIN copied NEV_AccumulateRaw.FunsExternal
-- Concrete callee bindings for the imported actual-body extraction. No axioms
-- and no callback hypotheses. Their composition domains are separate goals.
set_option autoImplicit false
noncomputable section
namespace NEV_AccumulateRaw
open Aeneas Aeneas.Std Result
namespace NEV_Bindings
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact

def toCtorQ (q : Q) : NEV_CodeFieldRaw.aspis_core.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromCtorE (e : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact) : E :=
 ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,
  ⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def toNativeQ (q : Q) : FIo_Native.aspis_core.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromNativeQ (q : FIo_Native.aspis_core.field.QM31) : Q :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toNativeE (e : E) : FIo_Native.aspis_core.field.wide_exact.WideExact :=
 ⟨toNativeQ e.c0,toNativeQ e.c1⟩
def fromNativeE (e : FIo_Native.aspis_core.field.wide_exact.WideExact) : E :=
 ⟨fromNativeQ e.c0,fromNativeQ e.c1⟩
def toPushQ (q : Q) : NEI_PushRaw.aspis_core.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
end NEV_Bindings

-- Frozen field calls already have direct closed callee bridges. Constructors
-- use the newly emitted normalization path, not an assumed canonical identity.
def aspis_core.field.wide_exact.WideExact.from_qm31 (q : NEV_Bindings.Q) : Result NEV_Bindings.E := do
 let e ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31 (NEV_Bindings.toCtorQ q)
 ok (NEV_Bindings.fromCtorE e)
def aspis_core.field.wide_exact.WideExact.add (x y : NEV_Bindings.E) : Result NEV_Bindings.E := do
 let e ← FIo_Native.aspis_core.field.wide_exact.WideExact.add (NEV_Bindings.toNativeE x) (NEV_Bindings.toNativeE y)
 ok (NEV_Bindings.fromNativeE e)
def aspis_core.field.wide_exact.WideExact.mul_qm31 (x : NEV_Bindings.E) (y : NEV_Bindings.Q) : Result NEV_Bindings.E := do
 let e ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (NEV_Bindings.toNativeE x) (NEV_Bindings.toNativeQ y)
 ok (NEV_Bindings.fromNativeE e)
def aspis_core.field.M31.ZERO : Result U32 := ok 0#u32
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
abbrev aspis_core.field.M31.sub := NEI_LineFull.aspis_core.field.M31.sub
abbrev aspis_core.field.M31.mul := NEI_LineFull.aspis_core.field.M31.mul
abbrev aspis_core.field.M31.double := NEI_LineFull.aspis_core.field.M31.double

def aspis_core.field.QM31.mul (x y : NEV_Bindings.Q) : Result NEV_Bindings.Q := do
 let q ← FIo_Native.aspis_core.field.QM31.mul (NEV_Bindings.toNativeQ x) (NEV_Bindings.toNativeQ y)
 ok (NEV_Bindings.fromNativeQ q)
def aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 (x : U32) : Result NEV_Bindings.E := do
 let e ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x
 ok (NEV_Bindings.fromCtorE e)
-- program-build disables the diagnostic trace body. This is source parity,
-- not runtime oracle trust or a successful-result premise.
def trace.value (_ : U16) (_ : Usize) (_ : NEV_Bindings.E) : Result Unit := ok ()
def BatchedWeights.push (b : BatchedWeights) (j : Usize) (q : NEV_Bindings.Q) (m : U32) : Result BatchedWeights := do
 let out ← NEI_PushRaw.BatchedWeights.push ⟨b.raw,b.terms⟩ j (NEV_Bindings.toPushQ q) m
 ok ⟨out.raw,out.terms⟩
end NEV_AccumulateRaw
end
-- END copied NEV_AccumulateRaw.FunsExternal
-- BEGIN copied NBG_Embedding
set_option autoImplicit false
noncomputable section
namespace NFS_NBG_Embedding
open Aeneas Aeneas.Std Result AspisS1M31Embedding

/-- Inventory correction: the coherent closure already contains this exact
trait member in S1M31EmbeddingSourceV1; it was missed by NBI2's name scan. -/
theorem from_m31_result (x : U32) :
    aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
      ok (AspisS1M31Embedding.Total.value x) :=
  AspisS1M31Embedding.Total.source_total x

/-- All raw QM31 limbs are normalized, and all four upper limbs are zero. -/
theorem from_qm31_result (x : aspis_core.field.QM31) :
    aspis_core.field.wide_exact.WideExact.from_qm31 x =
      ok (⟨⟨⟨Total.reduce x.c0.a,Total.reduce x.c0.b⟩,
          ⟨Total.reduce x.c1.a,Total.reduce x.c1.b⟩⟩,
        ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩ : aspis_core.field.wide_exact.WideExact) := by
  simp only [aspis_core.field.wide_exact.WideExact.from_qm31,
    aspis_core.field.wide_exact.canonical_qm31,
    aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    Total.rem_total,bind_tc_ok,aspis_core.field.QM31.ZERO]

#print axioms from_m31_result
#print axioms from_qm31_result
#print axioms AspisS1M31Embedding.Total.reduce_val
end NFS_NBG_Embedding
-- END copied NBG_Embedding
-- BEGIN copied NEV_CodeFieldBridge
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_CodeFieldBridge
open Aeneas Aeneas.Std Result
abbrev RawE := NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact
abbrev StageE := NBF_RowInstall.E

def value (x : U32) : RawE :=
  ⟨⟨⟨AspisS1M31Embedding.Total.reduce x,0#u32⟩,⟨0#u32,0#u32⟩⟩,
    ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

def toStage (x : RawE) : StageE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

def fromStage (x : StageE) : RawE :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩

theorem raw_roundtrip (x : RawE) : fromStage (toStage x)=x := by cases x;rfl

theorem stage_roundtrip (x : StageE) : toStage (fromStage x)=x := by cases x;rfl

/-- Reuse the existing generic remainder law; no arithmetic is reproved. -/
theorem rem (x : U32) : x % NEV_CodeFieldRaw.aspis_core.field.P =
    ok (AspisS1M31Embedding.Total.reduce x) := by
  simpa only [NEV_CodeFieldRaw.aspis_core.field.P,AspisS1M31Embedding.aspis_core.field.P]
    using AspisS1M31Embedding.Total.rem_total x

/-- Complete newly emitted frozen trait path on ALL raw words, including both
normalization passes. All reached definitions are emitted, not templates. -/
theorem total (x : U32) :
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x =
      ok (value x) := by
  simp only [NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.CM31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.CM31.from_m31,
    NEV_CodeFieldRaw.aspis_core.field.QM31.from_cm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    NEV_CodeFieldRaw.aspis_core.field.M31.ZERO,
    NEV_CodeFieldRaw.aspis_core.field.CM31.ZERO,
    NEV_CodeFieldRaw.aspis_core.field.QM31.ZERO,
    rem,bind_tc_ok,AspisS1M31Embedding.Total.reduce_idempotent,
    AspisS1M31Embedding.Total.reduce_zero,value]

/-- This is the exact concrete callback installed in the adopted accumulation
cohort. Canonicality is required and must come from the caller's basis proof. -/
theorem cohort (ops : AspisR1.Port3_NativeQueryBody.Ops) (x : U32)
    (canonical : x.val<2147483647) :
    (do let out ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x
        ok (toStage out)) = (NBF_RowInstall.install ops).op10 x := by
  have reduced : AspisS1M31Embedding.Total.reduce x=x := by
    apply UScalar.eq_of_val_eq
    rw [AspisS1M31Embedding.Total.reduce_val]
    exact Nat.mod_eq_of_lt canonical
  rw [total,bind_tc_ok]
  simp only [toStage,value,reduced,NBF_RowInstall.install,NBF_RowInstall.embedM,NBF_RowInstall.zeroQ]

#print axioms raw_roundtrip
#print axioms stage_roundtrip
#print axioms rem
#print axioms total
#print axioms cohort
end NFS_NEV_CodeFieldBridge
end
-- END copied NEV_CodeFieldBridge
-- BEGIN copied NEV_AccumulateCallees
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_AccumulateCallees
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open NEV_AccumulateRaw.NEV_Bindings

def toCtorE (e : RawE) : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact :=
 ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,
  ⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def toPushBW (b : NEV_AccumulateRaw.BatchedWeights) : NEI_PushRaw.BatchedWeights :=
 ⟨b.raw,b.terms⟩

theorem native_e_reverse (x : FIo_Native.aspis_core.field.wide_exact.WideExact) :
    toNativeE (fromNativeE x)=x := by cases x;rfl
theorem native_q_reverse (x : FIo_Native.aspis_core.field.QM31) :
    toNativeQ (fromNativeQ x)=x := by cases x;rfl
theorem ctor_e_reverse (x : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact) :
    toCtorE (fromCtorE x)=x := by cases x;rfl

/-- These new laws transport only nominal raw extraction records. Each RHS
is the CLOSED concrete callee, with errors/divergence preserved, never an
assumed result or a supplied arithmetic equality. -/
theorem wide_add (x y : RawE) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add x y
        ok (toNativeE out)) =
      FIo_Native.aspis_core.field.wide_exact.WideExact.add (toNativeE x) (toNativeE y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.add
  cases run : FIo_Native.aspis_core.field.wide_exact.WideExact.add (toNativeE x) (toNativeE y) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,native_e_reverse]
theorem wide_product (x : RawE) (q : RawQ) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31 x q
        ok (toNativeE out)) =
      FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (toNativeE x) (toNativeQ q) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.mul_qm31
  cases run : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (toNativeE x) (toNativeQ q) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,native_e_reverse]
theorem qm_product (x y : RawQ) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.QM31.mul x y
        ok (toNativeQ out)) =
      FIo_Native.aspis_core.field.QM31.mul (toNativeQ x) (toNativeQ y) := by
  unfold NEV_AccumulateRaw.aspis_core.field.QM31.mul
  cases run : FIo_Native.aspis_core.field.QM31.mul (toNativeQ x) (toNativeQ y) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,native_q_reverse]
theorem from_qm (q : RawQ) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31 q
        ok (toCtorE out)) =
      NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31 (toCtorQ q) := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31
  cases run : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31 (toCtorQ q) <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div,ctor_e_reverse]
theorem push (b : NEV_AccumulateRaw.BatchedWeights) (j : Usize) (q : RawQ) (m : U32) :
    (do let out ← NEV_AccumulateRaw.BatchedWeights.push b j q m
        ok (toPushBW out)) =
      NEI_PushRaw.BatchedWeights.push (toPushBW b) j (toPushQ q) m := by
  unfold NEV_AccumulateRaw.BatchedWeights.push
  cases run : NEI_PushRaw.BatchedWeights.push (toPushBW b) j (toPushQ q) m <;>
    simp only [toPushBW] at run ⊢ <;>
    simp only [run,bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem from_m31 (ops : AspisR1.Port3_NativeQueryBody.Ops) (m : U32)
    (canonical : m.val<2147483647) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 m
        ok (NEV_AccumulateCarriers.toE out)) =
      (NBF_RowInstall.install ops).op10 m := by
  unfold NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
  simp only [bind_assoc_eq,bind_tc_ok]
  exact NFS_NEV_CodeFieldBridge.cohort ops m canonical

#print axioms native_e_reverse
#print axioms native_q_reverse
#print axioms ctor_e_reverse
#print axioms wide_add
#print axioms wide_product
#print axioms qm_product
#print axioms from_qm
#print axioms push
#print axioms from_m31
end NFS_NEV_AccumulateCallees
end
-- END copied NEV_AccumulateCallees
-- BEGIN copied NEV_PushUse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_PushUse
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers

def fromNEG (b : NEG_PushActual.BatchedWeights) : AspisR1Stage2.verifier.BatchedWeights :=
 ⟨b.raw,b.terms⟩

/-- Reuse the CLOSED NEI/NEG push association on the SAME carrier and inputs.
Only nominal record conversions compose here, preserving every Result tag.
The bounded row-domain obligation remains separately caller-established. -/
theorem association (b : NEV_AccumulateRaw.BatchedWeights) (index : Usize)
    (power : RawQ) (basis : U32) :
    (do let out ← NEV_AccumulateRaw.BatchedWeights.push b index power basis
        ok (toWeights out)) =
      AspisR1.Port3_NativeRowFrame.push (toWeights b) index (toQ power) basis := by
  have base := NEI_PushRawAssociation.push
    (⟨b.raw,b.terms⟩ : NEI_PushRaw.BatchedWeights) index
    (NEV_AccumulateRaw.NEV_Bindings.toPushQ power) basis
  rw [NEG_PushAssociation.source] at base
  have lifted := congrArg (fun result : Result NEG_PushActual.BatchedWeights =>
    do let out ← result;ok (fromNEG out)) base
  simpa only [NEV_AccumulateRaw.BatchedWeights.push,toWeights,fromNEG,
    NEI_PushRawAssociation.toBW,NEI_PushRawAssociation.toPower,
    NEV_AccumulateRaw.NEV_Bindings.toPushQ,toQ,
    AspisR1.Port3_NativeRowFrame.push,AspisR1.Port3_RowsInstall.toBW,
    AspisR1.Port3_RowsInstall.fromBW,AspisR1.Port3_RowsInstall.toK,
    NEG_RowAssociation.toOld,Port26ROW.toK,bind_assoc_eq,bind_tc_ok] using lifted
#print axioms association
end NFS_NEV_PushUse
end
-- END copied NEV_PushUse
-- BEGIN copied NEV_AccumulateRaw.Funs
-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [neg_isolated]: function definitions
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

namespace NEV_AccumulateRaw

/-- [neg_isolated::basis_at]:
    Source: 'src/lib.rs', lines 66:0-66:61 -/
def basis_at
  (basis : Array aspis_core.field.M31 256#usize) (index : Std.Usize) :
  Result aspis_core.field.M31
  := do
  Array.index_usize basis index

/-- [neg_isolated::accumulated_weight_at]:
    Source: 'src/lib.rs', lines 67:0-67:70 -/
def accumulated_weight_at
  (weights : Slice aspis_core.field.QM31) (index : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  Slice.index_usize weights index

/-- [neg_isolated::accumulate_batched_with_node]: loop body 1:
    Source: 'src/lib.rs', lines 71:19-71:65 -/
@[rust_loop_body]
def accumulate_batched_with_node_loop0_loop0.body
  (node : aspis_core.field.M31) (n : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.M31 256#usize)) (Array aspis_core.field.M31 256#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done basis)
  | some j =>
    let m ← Array.index_usize basis j
    let m1 ← aspis_core.field.M31.mul m node
    let i ← n + j
    let basis1 ← Array.update basis i m1
    ok (cont (iter1, basis1))

/-- [neg_isolated::accumulate_batched_with_node]: loop 1:
    Source: 'src/lib.rs', lines 71:19-71:65 -/
@[rust_loop]
def accumulate_batched_with_node_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (iter1, basis1) => accumulate_batched_with_node_loop0_loop0.body node
      n iter1 basis1)
    (iter, basis)

/-- [neg_isolated::accumulate_batched_with_node]: loop body 0:
    Source: 'src/lib.rs', lines 71:4-71:115 -/
@[rust_loop_body]
def accumulate_batched_with_node_loop0.body
  (m : aspis_core.field.M31) (width : Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (ControlFlow (aspis_core.field.M31 × (Array aspis_core.field.M31
    256#usize) × Std.Usize) (Array aspis_core.field.M31 256#usize))
  := do
  if n < width
  then
    let basis1 ←
      accumulate_batched_with_node_loop0_loop0
        { start := 0#usize, «end» := n } node basis n
    let m1 ← aspis_core.field.M31.mul node node
    let m2 ← aspis_core.field.M31.double m1
    let node1 ← aspis_core.field.M31.sub m2 m
    let n1 ← n * 2#usize
    ok (cont (node1, basis1, n1))
  else ok (done basis)

/-- [neg_isolated::accumulate_batched_with_node]: loop 0:
    Source: 'src/lib.rs', lines 71:4-71:115 -/
@[rust_loop]
def accumulate_batched_with_node_loop0
  (m : aspis_core.field.M31) (node : aspis_core.field.M31) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (node1, basis1, n1) => accumulate_batched_with_node_loop0.body m width
      node1 basis1 n1)
    (node, basis, n)

/-- [neg_isolated::accumulate_batched_with_node]: loop body 2:
    Source: 'src/lib.rs', lines 72:4-77:5 -/
@[rust_loop_body]
def accumulate_batched_with_node_loop1.body
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize)
  (iter : core.ops.range.Range Std.Usize) (weights : BatchedWeights) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × BatchedWeights)
    BatchedWeights)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done weights)
  | some j =>
    let m ← basis_at basis j
    let weights1 ← BatchedWeights.push weights j q m
    let i1 ← i * width
    let i2 ← i1 + j
    let s := alloc.vec.Vec.deref v
    let q1 ← accumulated_weight_at s j
    let we ← aspis_core.field.wide_exact.WideExact.from_qm31 q1
    trace.value 12#u16 i2 we
    let i3 ← i1 + j
    let we1 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        m
    trace.value 13#u16 i3 we1
    ok (cont (iter1, weights1))

/-- [neg_isolated::accumulate_batched_with_node]: loop 2:
    Source: 'src/lib.rs', lines 72:4-77:5 -/
@[rust_loop]
def accumulate_batched_with_node_loop1
  (iter : core.ops.range.Range Std.Usize)
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (weights : BatchedWeights) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result BatchedWeights
  := do
  loop
    (fun (iter1, weights1) => accumulate_batched_with_node_loop1.body v q i
      width basis iter1 weights1)
    (iter, weights)

/-- [neg_isolated::accumulate_batched_with_node]:
    Source: 'src/lib.rs', lines 68:0-81:1 -/
def accumulate_batched_with_node
  (p : Prepared) (a : Accumulator) (node : aspis_core.field.M31)
  (value : aspis_core.field.wide_exact.WideExact) (weights : BatchedWeights) :
  Result (Accumulator × BatchedWeights)
  := do
  let width := alloc.vec.Vec.len a.weights
  let m ← aspis_core.field.M31.ZERO
  let basis := Array.repeat 256#usize m
  let m1 ← aspis_core.field.M31.ONE
  let basis1 ← Array.update basis 0#usize m1
  let basis2 ←
    accumulate_batched_with_node_loop0 m1 node width basis1 1#usize
  let weights1 ←
    accumulate_batched_with_node_loop1 { start := 0#usize, «end» := width }
      a.weights a.power a.next weights width basis2
  let i ← weights1.terms + 1#usize
  let we ← aspis_core.field.wide_exact.WideExact.mul_qm31 value a.power
  let we1 ← aspis_core.field.wide_exact.WideExact.add a.rhs we
  trace.value 11#u16 a.next we1
  let q ← aspis_core.field.QM31.mul a.power p.rho
  let i1 ← a.next + 1#usize
  ok ({ a with rhs := we1, power := q, next := i1 },
    { weights1 with terms := i })

end NEV_AccumulateRaw
-- END copied NEV_AccumulateRaw.Funs
-- BEGIN copied NEV_BorrowMaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_BorrowMaps
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
/-- Same indexed value through the full-vector nominal carrier map. -/
theorem vector_read {A B : Type} (f : A → B) (v : alloc.vec.Vec A) (index : Usize)
    (inside : index.val<v.val.length) :
    ∃ value, Slice.index_usize v.deref index=ok value ∧
      Slice.index_usize (mapVec f v).deref index=ok (f value) := by
  obtain ⟨value,read,point⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v index inside)
  have mappedInside : index.val<(mapVec f v).val.length := by
    simpa only [mapVec,List.length_map] using inside
  obtain ⟨mapped,mappedRead,mappedAt⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec (mapVec f v) index mappedInside)
  have mappedAt' : mapped=f (v.val[index.val]'inside) := by
    simpa only [mapVec,List.getElem_map] using mappedAt
  have same : mapped=f value := mappedAt'.trans (congrArg f point.symm)
  refine ⟨value,read,?_⟩
  exact mappedRead.trans (congrArg Result.ok same)

/-- The actual reached getter and the installed cohort read have the SAME
input index and returned four raw words, on the caller's length domain. -/
theorem weight_read (ops : AspisR1.Port3_NativeQueryBody.Ops)
    (v : alloc.vec.Vec RawQ) (index : Usize) (inside : index.val<v.val.length) :
    ∃ q, NEV_AccumulateRaw.accumulated_weight_at v.deref index=ok q ∧
      (NBF_RowInstall.install ops).op12 (mapVec toQ v).deref index=ok (toQ q) := by
  obtain ⟨q,read,mapped⟩ := vector_read toQ v index inside
  exact ⟨q,read,mapped⟩
#print axioms vector_read
#print axioms weight_read
end NFS_NEV_BorrowMaps
end
-- END copied NEV_BorrowMaps
-- BEGIN copied NEV_CtorNormalization
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_CtorNormalization
open Aeneas Aeneas.Std Result
abbrev Q := NEV_CodeFieldRaw.aspis_core.field.QM31

def normalized (q : Q) : Q :=
 ⟨⟨AspisS1M31Embedding.Total.reduce q.c0.a,AspisS1M31Embedding.Total.reduce q.c0.b⟩,
  ⟨AspisS1M31Embedding.Total.reduce q.c1.a,AspisS1M31Embedding.Total.reduce q.c1.b⟩⟩
def Canonical (q : Q) : Prop :=
 (q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647) ∧
 (q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647)
/-- Nominal constructor transport only; each remainder uses the retained
all-machine-word S1 law, rather than a new arithmetic proof. -/
theorem total (q : Q) :
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31 q=ok (normalized q) := by
  simp only [NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    NFS_NEV_CodeFieldBridge.rem,bind_tc_ok,normalized]
theorem reduce_identity (word : U32) (small : word.val<2147483647) :
    AspisS1M31Embedding.Total.reduce word=word := by
  apply UScalar.eq_of_val_eq
  rw [AspisS1M31Embedding.Total.reduce_val]
  exact Nat.mod_eq_of_lt small
theorem identity (q : Q) (canonical : Canonical q) : normalized q=q := by
  simp only [normalized,reduce_identity q.c0.a canonical.1.1,
    reduce_identity q.c0.b canonical.1.2,reduce_identity q.c1.a canonical.2.1,
    reduce_identity q.c1.b canonical.2.2]

/-- Equality to the adopted row callback on the SAME canonical read value. -/
theorem cohort (ops : AspisR1.Port3_NativeQueryBody.Ops)
    (q : NEV_AccumulateCarriers.RawQ)
    (canonical : Canonical (NEV_AccumulateRaw.NEV_Bindings.toCtorQ q)) :
    (do let e ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31 q
        ok (NEV_AccumulateCarriers.toE e)) =
      (NBF_RowInstall.install ops).op1 (NEV_AccumulateCarriers.toQ q) := by
  simp only [NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    total,identity _ canonical,bind_tc_ok,NEV_CodeFieldRaw.aspis_core.field.QM31.ZERO]
  rfl

#print axioms total
#print axioms reduce_identity
#print axioms identity
#print axioms cohort
end NFS_NEV_CtorNormalization
end
-- END copied NEV_CtorNormalization
-- BEGIN copied NEV_CtorResults
set_option autoImplicit false
noncomputable section
namespace NFS_NEV_CtorResults
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
open NEV_AccumulateRaw.NEV_Bindings

def mValue (word : U32) : RawE := fromCtorE (NFS_NEV_CodeFieldBridge.value word)
def qValue (q : RawQ) : RawE :=
 fromCtorE ⟨NFS_NEV_CtorNormalization.normalized (toCtorQ q),NEV_CodeFieldRaw.aspis_core.field.QM31.ZERO⟩
/-- Reuse constructor totality on all raw words; only the nominal output
carrier is different at this actual accumulation call site. -/
theorem m31 (word : U32) :
    NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 word=
      ok (mValue word) := by
  simp only [NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31,
    NFS_NEV_CodeFieldBridge.total,bind_tc_ok,mValue]
theorem qm (q : RawQ) :
    NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31 q=ok (qValue q) := by
  simp only [NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31,
    NFS_NEV_CtorNormalization.total,bind_tc_ok,qValue]
#print axioms m31
#print axioms qm
end NFS_NEV_CtorResults
end
-- END copied NEV_CtorResults
-- BEGIN copied NEV_RowStep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_RowStep
open Aeneas Aeneas.Std Result ControlFlow NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev Iter := core.ops.range.Range Usize
abbrev RawFlow := ControlFlow (Iter × NEV_AccumulateRaw.BatchedWeights) NEV_AccumulateRaw.BatchedWeights
abbrev Flow := ControlFlow (Iter × AspisR1Stage2.verifier.BatchedWeights) AspisR1Stage2.verifier.BatchedWeights

def mapFlow : RawFlow → Flow
 | .cont (iter,b) => .cont (iter,toWeights b)
 | .done b => .done (toWeights b)

/-- One actual row iteration, preserving complete Result and returned BW.
Diagnostic conversions execute in the source, are total on all raw words,
and feed the deployed no-op trace; no diagnostic value is an observable. -/
theorem active (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next : Usize)
    (basis : Array U32 256#usize) (iter : Iter) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : v.val.length=64) (finish : iter.end=64#usize)
    (inside : iter.start.val<64) (global : next.val<22) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
          v power next 64#usize basis iter b
        ok (mapFlow out)) =
      verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
        (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b) := by
  obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_some_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
      iter (by rw [finish];exact inside))
  subst o
  obtain ⟨word,basisRead,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec basis iter.start (by change iter.start.val<basis.val.length;rw [basis.property];change iter.start.val<256;omega))
  obtain ⟨q,read,mappedRead⟩ := NFS_NEV_BorrowMaps.weight_read ops v iter.start (by omega)
  have mappedRead' : core.slice.index.Slice.index
      (core.slice.index.SliceIndexUsizeSlice NBF_RowInstall.Q)
      (mapVec toQ v).deref iter.start=ok (toQ q) := mappedRead
  have multiplication := NBF_BasisInstall.checked_mul next 64#usize
    (by change next.val*64≤4096;omega)
  have productValue := Port3_Wrapping.wrap_mul_value next 64#usize
    (by change next.val*64≤4096;omega)
  have offset := Port3_Wrapping.checked_add (Usize.wrapping_mul next 64#usize) iter.start
    (by rw [productValue];change next.val*64+iter.start.val≤4096;omega)
  have use := NFS_NEV_PushUse.association b iter.start power word
  have lifted := congrArg (fun result : Result AspisR1Stage2.verifier.BatchedWeights =>
    do let out ← result;ok (cont (iter1,out) : Flow)) use
  simpa [NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body,
    verifier.accumulate_batched_with_node_loop1.body,NBF_RowInstall.install,
    run,NEV_AccumulateRaw.basis_at,basisRead,read,mappedRead',
    multiplication,offset,lift,NFS_NEV_CtorResults.qm,NFS_NEV_CtorResults.m31,
    NEV_AccumulateRaw.trace.value,bind_assoc_eq,mapFlow] using lifted

theorem stop (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next width : Usize)
    (basis : Array U32 256#usize) (iter : Iter) (b : NEV_AccumulateRaw.BatchedWeights)
    (halt : iter.end.val≤ iter.start.val) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
          v power next width basis iter b
        ok (mapFlow out)) =
      verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
        (mapVec toQ v) (toQ power) next width basis iter (toWeights b) := by
  obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
      (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter halt)
  subst o
  simp only [NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body,
    verifier.accumulate_batched_with_node_loop1.body,run,bind_tc_ok]
  rfl
#print axioms active
#print axioms stop
end NFS_NEV_RowStep
end
-- END copied NEV_RowStep
-- BEGIN copied NEV_RowLoop
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFS_NEV_RowLoop
open Aeneas Aeneas.Std Result ControlFlow NEV_AccumulateCarriers
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Only control-flow/carrier transport is new. The imported push bridge and
its existing row arithmetic/phase induction are reused unchanged. -/
theorem association (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next : Usize)
    (basis : Array U32 256#usize) (fuel : Nat) (iter : NFS_NEV_RowStep.Iter)
    (b : NEV_AccumulateRaw.BatchedWeights) (width : v.val.length=64)
    (raw : b.raw.val.length=64) (finish : iter.end=64#usize)
    (span : iter.start.val+fuel=64) (global : next.val<22) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1
          iter v power next b 64#usize basis
        ok (toWeights out)) =
      verifier.accumulate_batched_with_node_loop1 (NBF_RowInstall.install ops)
        iter (mapVec toQ v) (toQ power) next (toWeights b) 64#usize basis := by
  induction fuel generalizing iter b with
  | zero =>
    have halt : iter.end.val≤ iter.start.val := by rw [finish];change 64≤ iter.start.val;omega
    obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
      (core.iter.range.IteratorRange.next_UScalar_none_spec
        (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
        (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter halt)
    subst o
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop1
      verifier.accumulate_batched_with_node_loop1
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    simp [NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body,
      verifier.accumulate_batched_with_node_loop1.body,run]
  | succ k ih =>
    have inside : iter.start.val<64 := by omega
    have mapped := NFS_NEV_RowStep.active ops v power next basis iter b width finish inside global
    unfold NEV_AccumulateRaw.accumulate_batched_with_node_loop1
      verifier.accumulate_batched_with_node_loop1
    rw [Aeneas.Std.loop.eq_def,Aeneas.Std.loop.eq_def]
    dsimp only
    cases bodyRun : NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
        v power next 64#usize basis iter b with
    | fail error =>
      have modelRun : verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)=fail error := by
        simpa only [bodyRun,bind_tc_fail] using mapped.symm
      simp only [modelRun,bind_tc_fail]
    | div =>
      have modelRun : verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)=div := by
        simpa only [bodyRun,bind_tc_div] using mapped.symm
      simp only [modelRun,bind_tc_div]
    | ok flow =>
      have modelRun : verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)=ok (NFS_NEV_RowStep.mapFlow flow) := by
        simpa only [bodyRun,bind_tc_ok] using mapped.symm
      obtain ⟨iter1,after,shape,counter,endpoint,length,terms⟩ :=
        Port3_NativeRowFrame.body_fields (NBF_RowInstall.install ops)
          (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)
          (by rw [finish];exact inside)
          (by rw [finish];change 64≤b.raw.val.length;omega)
          (NFS_NEV_RowStep.mapFlow flow) modelRun
      cases flow with
      | done final => cases shape
      | cont pair =>
        rcases pair with ⟨cursor,result⟩
        have same : (cursor,toWeights result)=(iter1,after) := ControlFlow.cont.inj shape
        have cursors : cursor=iter1 := congrArg Prod.fst same
        have carriers : toWeights result=after := congrArg Prod.snd same
        rw [← cursors] at counter endpoint
        rw [← carriers] at length
        have size : result.raw.val.length=64 := by
          change result.raw.val.length=b.raw.val.length at length
          exact length.trans raw
        simp only [modelRun,NFS_NEV_RowStep.mapFlow,bind_tc_ok]
        exact ih cursor result size (endpoint.trans finish) (by omega)
#print axioms association
end NFS_NEV_RowLoop
end
-- END copied NEV_RowLoop
-- BEGIN copied NEI_FieldCarriers
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_FieldCarriers
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
namespace N
abbrev C := NEI_LineFull.aspis_core.field.CM31
abbrev Q := NEI_LineFull.aspis_core.field.QM31
abbrev E := NEI_LineFull.aspis_core.field.wide_exact.WideExact
end N
namespace C
abbrev C := AspisR1CurrentWide.field.CM31
abbrev Q := AspisR1CurrentWide.field.QM31
abbrev E := AspisR1CurrentWide.field.wide_exact.WideExact
end C

def toC (x : N.C) : C.C := ⟨x.a,x.b⟩
def fromC (x : C.C) : N.C := ⟨x.a,x.b⟩
def toQ (x : N.Q) : C.Q := ⟨toC x.c0,toC x.c1⟩
def fromQ (x : C.Q) : N.Q := ⟨fromC x.c0,fromC x.c1⟩
def toE (x : N.E) : C.E := ⟨toQ x.c0,toQ x.c1⟩
def fromE (x : C.E) : N.E := ⟨fromQ x.c0,fromQ x.c1⟩

theorem fromtoC (x : N.C) : fromC (toC x) = x := by
  cases x
  rfl

theorem tofromC (x : C.C) : toC (fromC x) = x := by
  cases x
  rfl

theorem bindC {B B' : Type} (F : B → B') (r : Result N.C) (k : N.C → Result B) :
    resultMap F (r >>= k) =
      (resultMap toC r) >>= (fun y => resultMap F (k (fromC y))) :=
  resultMap_bind_transport toC fromC fromtoC F r k

theorem fromtoQ (x : N.Q) : fromQ (toQ x) = x := by
  cases x
  rfl

theorem tofromQ (x : C.Q) : toQ (fromQ x) = x := by
  cases x
  rfl

theorem bindQ {B B' : Type} (F : B → B') (r : Result N.Q) (k : N.Q → Result B) :
    resultMap F (r >>= k) =
      (resultMap toQ r) >>= (fun y => resultMap F (k (fromQ y))) :=
  resultMap_bind_transport toQ fromQ fromtoQ F r k

theorem fromtoE (x : N.E) : fromE (toE x) = x := by
  cases x
  rfl

theorem tofromE (x : C.E) : toE (fromE x) = x := by
  cases x
  rfl

theorem bindE {B B' : Type} (F : B → B') (r : Result N.E) (k : N.E → Result B) :
    resultMap F (r >>= k) =
      (resultMap toE r) >>= (fun y => resultMap F (k (fromE y))) :=
  resultMap_bind_transport toE fromE fromtoE F r k

theorem okC (a b : U32) : resultMap toC (ok (⟨a,b⟩ : N.C)) = ok (⟨a,b⟩ : C.C) := rfl

theorem okQ (a b : N.C) : resultMap toQ (ok (⟨a,b⟩ : N.Q)) = ok (⟨toC a,toC b⟩ : C.Q) := rfl

theorem okE (a b : N.Q) : resultMap toE (ok (⟨a,b⟩ : N.E)) = ok (⟨toQ a,toQ b⟩ : C.E) := rfl

theorem bindWord {B B' : Type} (F : B → B') (r : Result U32) (k : U32 → Result B) :
    resultMap F (r >>= k) = r >>= (fun y => resultMap F (k y)) :=
  resultMap_bind F r k
#print axioms bindWord

#print axioms fromtoC
#print axioms tofromC
#print axioms bindC
#print axioms fromtoQ
#print axioms tofromQ
#print axioms bindQ
#print axioms fromtoE
#print axioms tofromE
#print axioms bindE
#print axioms okC
#print axioms okQ
#print axioms okE
end NFS_NEI_FieldCarriers
end
-- END copied NEI_FieldCarriers

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
