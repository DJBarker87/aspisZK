import Port3_RowsFrame

/-! The row callback is fixed to S7's complete emitted owned row driver.
The callback carrier maps are literal limb copies; arithmetic leaf meanings
and the local mutable/owned P6 lowering retain their original scope. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_RowsInstall
open Aeneas Aeneas.Std Result
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev BW := VTop_Stages.verifier.BatchedWeights

def toK (q : K) : S7Kani2AccumulatorLoop.K := ⟨(q.c0.a,q.c0.b),(q.c1.a,q.c1.b)⟩
def toWeights (v : alloc.vec.Vec K) : alloc.vec.Vec S7Kani2AccumulatorLoop.K :=
  ⟨v.val.map toK,by simpa using v.property⟩
def toBW (b : BW) : S7Kani2AccumulatorLoop.BatchedWeights := ⟨b.raw,b.terms⟩
def fromBW (b : S7Kani2AccumulatorLoop.BatchedWeights) : BW := ⟨b.raw,b.terms⟩

def rows (_iter : core.ops.range.Range Usize) (output : alloc.vec.Vec K)
    (power : K) (next : Usize) (pending : BW) (width : Usize)
    (basis : Array U32 256#usize) : Result BW := do
  let out ← S7Kani2AccumulatorLoop.accumulate_rows_owned S7JoinRowsTrace.backend
    (toWeights output) (toBW pending) basis (toK power) next width _iter.start
  ok (fromBW out.2)

def arithmetic (base : AspisR1Stage2.AccumulateOps) : AspisR1Stage2.AccumulateOps :=
  {base with weightLoop := rows}

theorem accepted_rows (output : alloc.vec.Vec K) (power : K) (next : Usize)
    (pending after : BW) (basis : Array U32 256#usize)
    (size : pending.raw.val.length=64)
    (success : rows {start:=0#usize,«end»:=64#usize} output power next pending 64#usize basis = ok after) :
    after.raw.val.length=64 ∧ after.terms=pending.terms := by
  unfold rows at success
  obtain ⟨out,run,success⟩ := Port3_PushFrame.bind_success _ _ _ success
  have fields := Port3_RowsFrame.rows_fields basis (toK power) next
    (toWeights output,toBW pending) out size run
  have same := Result.ok.inj success
  subst after
  exact ⟨fields.2.1,fields.2.2⟩

theorem accumulate_raw (base : AspisR1Stage2.AccumulateOps)
    (p : AspisR1Stage2.verifier.Prepared) (a out : AspisR1Stage2.verifier.Accumulator)
    (node : AspisR1Stage2.Stage2M) (value : AspisR1Stage2.Stage2E)
    (pending after : BW) (weights : a.weights.val.length=64) (size : pending.raw.val.length=64)
    (success : AspisR1Stage2.verifier.accumulateWithOps (arithmetic base) p a node value pending = ok (out,after)) :
    out.weights=a.weights ∧ after.raw.val.length=64 := by
  have frame := Port3_QueryFrame.accumulate_weights (arithmetic base) p a out node value pending after success
  unfold AspisR1Stage2.verifier.accumulateWithOps at success
  iterate 3 obtain ⟨x,_,success⟩ := Port3_PushFrame.bind_success _ _ _ success
  obtain ⟨basis,_,success⟩ := Port3_PushFrame.bind_success _ _ _ success
  obtain ⟨mid,hrows,success⟩ := Port3_PushFrame.bind_success _ _ _ success
  have width : alloc.vec.Vec.len a.weights = 64#usize := by
    apply UScalar.eq_of_val_eq
    exact weights
  have hrows' : rows {start:=0#usize,«end»:=64#usize} a.weights a.power a.next pending 64#usize basis = ok mid := by
    simpa only [arithmetic,width] using hrows
  have raw := (accepted_rows a.weights a.power a.next pending mid basis size hrows').1
  iterate 6 obtain ⟨x,_,success⟩ := Port3_PushFrame.bind_success _ _ _ success
  have same := Result.ok.inj success
  cases same
  exact ⟨frame,raw⟩

#print axioms accepted_rows
#print axioms accumulate_raw
end AspisR1.Port3_RowsInstall
end
