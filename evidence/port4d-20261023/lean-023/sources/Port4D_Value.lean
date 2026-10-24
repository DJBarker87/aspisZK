import Port4D_FlushRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_Value
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- TrustedStd four-element array-map content interpretation. The arithmetic
callback is the retained reducer; its current-source S5 pin stays separate. -/
def map4 (a : Array U64 4#usize) : Result (Array U32 4#usize) := do
  let x0 ← Array.index_usize a 0#usize
  let y0 ← S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64 x0
  let x1 ← Array.index_usize a 1#usize
  let y1 ← S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64 x1
  let x2 ← Array.index_usize a 2#usize
  let y2 ← S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64 x2
  let x3 ← Array.index_usize a 3#usize
  let y3 ← S8Kani2MutableExtraction.aspis_core.field.M31.reduce_u64 x3
  ok (Array.make 4#usize [y0,y1,y2,y3])
def native (map : Array U64 4#usize → Result (Array U32 4#usize))
  (self : verifier.BatchedWeights) (index : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let a ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U64
      4#usize)) self.«raw» index
  let a1 ←
    map a
  let a2 ← Array.index_usize a1 0#usize
  let b ← Array.index_usize a1 1#usize
  let c ← Array.index_usize a1 2#usize
  let d ← Array.index_usize a1 3#usize
  ok { c0 := { a := a2, b }, c1 := { a := c, b := d } }


theorem value_eq (b : verifier.BatchedWeights) (i : Usize) :
    native map4 b i = Port4D_FlushABI.value b i := by
  unfold native map4 Port4D_FlushABI.value S8Kani2MutableValue.F.value
    S8Kani2MutableExtraction.batched_weights.BatchedWeights.value
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl

def flush := Port3_NativeFlushBody.verifier.BatchedWeights.finish Port4D_FlushABI.std (native map4)

theorem callback_eq : native map4 = Port4D_FlushABI.value := by
  funext b i
  exact value_eq b i

theorem flush_eq (b : verifier.BatchedWeights) (old : Slice aspis_core.field.QM31) :
    flush b old = Port4D_FlushRows.flush b old := by
  unfold flush
  rw [callback_eq]
  rfl

theorem reference_eq (b : verifier.BatchedWeights) (old : Slice aspis_core.field.QM31)
    (lengths : old.val.length ≤ b.raw.val.length) :
    flush b old = Port3_FlushInstall.flush b old :=
  Port4D_FlushRows.lower_value (native map4) b old lengths (fun i _ => value_eq b i)

#print axioms value_eq
#print axioms callback_eq
#print axioms flush_eq
#print axioms reference_eq
end AspisR1.Port4D_Value
end
