import PairLowCallTypesClean
import S3PowersLowActualCanonicalV1
import S3PowersLowTotalV1
import S4FromFnP6GeneratedInterface
import CurrentPowersExactProduct

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowCallCut

/-! This is the exact emitted low callback body with its three field-operation
externals made explicit typed inputs.  No generated FunsExternal template is
imported, so no external-operation axioms enter the selected closure. -/

structure LowFieldOps where
  wideMul : field.WideExact → field.WideExact → Result field.WideExact
  m31Mul : field.M31 → field.M31 → Result field.M31
  wideMulM31 : field.WideExact → field.M31 → Result field.WideExact

def weights.QUARTER : field.M31 := 536870912#u32
def weights.PERM : Array Std.Usize 4#usize :=
  Array.make 4#usize [0#usize, 3#usize, 2#usize, 1#usize]

abbrev ActualS :=
  AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.S

def toActualS (x : field.WideExact) : ActualS :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def fromActualS (x : ActualS) : field.WideExact :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

theorem from_to_actual (x : field.WideExact) : fromActualS (toActualS x) = x := by
  cases x <;> rfl

theorem to_from_actual (x : ActualS) : toActualS (fromActualS x) = x := by
  cases x <;> rfl

def actualFieldOps : LowFieldOps := {
  wideMul := fun x y => do
    let z ← AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul
      (toActualS x) (toActualS y)
    .ok (fromActualS z)
  m31Mul := fun x y => AspisR1CurrentWide.field.M31.mul x y
  wideMulM31 := fun x s => do
    let z ← AspisR1S3PowersLowEntryCanonicalV1.mulM31 (toActualS x) s
    .ok (fromActualS z)
}

def generatedToPower (x : field.WideExact) :
    AspisR1PowersConcreteMul.CallbackWide :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

def powerToGenerated (x : AspisR1PowersConcreteMul.CallbackWide) :
    field.WideExact :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩,
    ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

theorem power_generated_roundtrip (x : AspisR1PowersConcreteMul.CallbackWide) :
    generatedToPower (powerToGenerated x) = x := by
  cases x <;> rfl

theorem generated_power_roundtrip (x : field.WideExact) :
    powerToGenerated (generatedToPower x) = x := by
  cases x <;> rfl

theorem generated_actual_field_roundtrip (x : ActualS) :
    toActualS (fromActualS x) = x := to_from_actual x

theorem actual_ops_mul_total_canonical (x y : field.WideExact)
    (hx : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
      (toActualS x))
    (hy : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
      (toActualS y)) :
    ∃ z, actualFieldOps.wideMul x y = .ok z ∧
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
        (toActualS z) := by
  obtain ⟨z, hz, hcan, _hdecode⟩ :=
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.mul_total_exact
      (toActualS x) (toActualS y) hx hy
  refine ⟨fromActualS z, ?_, ?_⟩
  · simp [actualFieldOps, hz]
  · simpa only [to_from_actual] using hcan

theorem actual_ops_m31mul_quarter_total :
    ∃ m, actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok m := by
  obtain ⟨m, hm, _hbound, _hvalue⟩ :=
    AspisR1.ExtractedCurrentReducer.current_mul_mod
      (536870912#u32) (536870912#u32)
  refine ⟨m, ?_⟩
  unfold actualFieldOps weights.QUARTER
  rw [AspisR1CurrentWide.Proof.m31_mul_same]
  exact hm

theorem actual_ops_mul_m31_total_canonical (x : field.WideExact)
    (s : field.M31)
    (hx : AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
      (toActualS x)) :
    ∃ z, actualFieldOps.wideMulM31 x s = .ok z ∧
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.Canonical
        (toActualS z) := by
  obtain ⟨z, hz⟩ := AspisR1S3PowersLowTotalV1.low_m31_total (toActualS x) s
  refine ⟨fromActualS z, ?_, ?_⟩
  · simp [actualFieldOps, hz]
  · have hcan := AspisR1S3PowersLowEntryCanonicalV1.mulM31_success_canonical
      (toActualS x) z s hx hz
    simpa only [to_from_actual] using hcan

def weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
    (ops : LowFieldOps) (c : weights.s2_twofold_low_array.closure)
    (tupled_args : Std.Usize) :
    Result (field.WideExact × weights.s2_twofold_low_array.closure) := do
  let (a, a1) := c
  let i ← tupled_args % 4#usize
  let i1 ← Array.index_usize weights.PERM i
  let we ← Array.index_usize a i1
  let i2 ← tupled_args / 4#usize
  let i3 ← Array.index_usize weights.PERM i2
  let we1 ← Array.index_usize a1 i3
  let we2 ← ops.wideMul we we1
  let m ← ops.m31Mul weights.QUARTER weights.QUARTER
  let we3 ← ops.wideMulM31 we2 m
  ok (we3, c)

def weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
    (ops : LowFieldOps) (c : weights.s2_twofold_low_array.closure)
    (i : Std.Usize) : Result field.WideExact := do
  let (we, _) ←
    weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
      ops c i
  ok we

def weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact
    (ops : LowFieldOps) :
    core.ops.function.FnOnce weights.s2_twofold_low_array.closure Std.Usize
      field.WideExact := {
  call_once := weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once ops
}

def weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
    (ops : LowFieldOps) :
    core.ops.function.FnMut weights.s2_twofold_low_array.closure Std.Usize
      field.WideExact := {
  FnOnceInst := weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact ops
  call_mut := weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut ops
}

def weights.s2_twofold_low_array_model (ops : LowFieldOps)
    (ap0 ap1 : Array field.WideExact 4#usize) :
    Result (Array field.WideExact 16#usize ×
      (weights.s2_twofold_low_array.closure × Std.Usize)) :=
  AspisR1FromFnP6Generated.core.array.from_fn_model 16#usize
    (weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops)
    (ap0, ap1)

end AspisR1PairLowCallCut

#print axioms AspisR1PairLowCallCut.weights.s2_twofold_low_array.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
