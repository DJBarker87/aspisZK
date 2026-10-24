import Port3_BatchStage

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Rejection
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)

/-- The emitted pending-return decoder, reproduced without changing it. -/
def emittedReturn (idx : Indices) (val : Values)
    (pending : Option (core.result.Result Unit verifier.Error)) :
    Result (core.result.Result Unit verifier.Error × Indices × Values) :=
  match pending with
  | none => fail .panic
  | some r => ok (r,idx,val)

/-- This is the actual final match of the installed emitted tree body. -/
theorem tree_return (ops : Port3_NativeBatchBody.Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (proof : Slice U8) (queries : Array U32 22#usize) (root : Array U8 32#usize)
    (batch tree lo hi n s : Usize) (idx : Indices) (val : Values)
    (keys sorted : Array U64 16#usize)
    (range : (if batch = 0#usize then do
        let i ← ops.op13; ok (0#usize,i)
      else do let i ← ops.op13; ok (i,22#usize)) = ok (lo,hi))
    (width : lift (Usize.wrapping_sub hi lo) = ok n)
    (slot : (do let i ← lift (Usize.wrapping_mul 3#usize batch)
                lift (Usize.wrapping_add i tree)) = ok s)
    (packed : ops.op4 queries lo n tree = ok keys)
    (sort : ops.op5 keys n = ok sorted) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree ops D proof queries root batch tree idx val hash =
      (do let (idx',val',pending) ←
            Port3_NativeBatchBody.verifier.candidate.batch_tree_loop ops D proof root tree idx val hash
              lo n s sorted 0#usize 0#usize
          emittedReturn idx' val' pending) := by
  simp only [Port3_NativeBatchBody.verifier.candidate.batch_tree,range,width,bind_tc_ok,packed,sort]
  -- Preserve the two physical wrapping operations rather than assuming a slot number.
  cases hm : lift (Usize.wrapping_mul 3#usize batch) with
  | fail e => simp_all
  | div => simp_all
  | ok i =>
    simp only [hm,bind_tc_ok] at slot ⊢
    rw [slot]
    rfl

/-- A missing pending return is a panic, never a Rust Parse/Merkle error. -/
theorem missing_return (idx : Indices) (val : Values) :
    emittedReturn idx val none = fail .panic ∧
    emittedReturn idx val none ≠ ok (.Err verifier.Error.Parse,idx,val) ∧
    emittedReturn idx val none ≠ ok (.Err verifier.Error.Merkle,idx,val) := by
  simp [emittedReturn]

#print axioms tree_return
#print axioms missing_return
end AspisR1.Port4B_Rejection
end
