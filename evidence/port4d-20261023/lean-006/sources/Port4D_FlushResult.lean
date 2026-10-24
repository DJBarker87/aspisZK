import Port4D_FlushLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FlushABI
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem finish_total (self : verifier.BatchedWeights)
    (value : verifier.BatchedWeights → Usize → Result K) (old : Slice K)
    (f : Nat → K) (values : ∀ i : Usize, i.val < old.val.length → value self i = ok (f i.val)) :
    Port3_NativeFlushBody.verifier.BatchedWeights.finish std value self old =
      ok (prefixWrite f 0 old.val.length old) := by
  let initial : FinishIter := ⟨{slice := old},0#usize⟩
  obtain ⟨back,run,contents⟩ := finish_loop_output_invariant_of_step_laws self value initial f
    (by simp [initial]) (by simp [initial])
    (some_step_law_actual (value self) _ f old.property (by simpa [initial] using values))
    (none_step_law_actual _)
  have cells := contents initial
  unfold Port3_NativeFlushBody.verifier.BatchedWeights.finish
  simp only [core.slice.Slice.iter_mut,bind_tc_ok, std, enumerate]
  change (do let back ← Port3_NativeFlushBody.verifier.BatchedWeights.finish_loop std value initial (fun e => e) self
             ok (back initial).iter.slice) = _
  rw [run]
  exact congrArg Result.ok cells

def value (self : verifier.BatchedWeights) (i : Usize) : Result K := do
  let q ← S8Kani2MutableValue.F.value ⟨self.raw,self.terms⟩ i
  ok (Port3_FlushInstall.fromMutable q)

theorem prefix_transport (f : Nat → S8Kani2MutableValue.F.Q) (start n : Nat)
    (s : S8Kani2MutableExtraction.batched_weights.FinishSlice) :
    Port3_FlushInstall.fromSlice (S8Kani2MutableExtraction.batched_weights.prefixWrite f start n s) =
      prefixWrite (fun j => Port3_FlushInstall.fromMutable (f j)) start n (Port3_FlushInstall.fromSlice s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [S8Kani2MutableExtraction.batched_weights.prefixWrite,prefixWrite]
    split
    · rw [ih]
      congr 1
      apply Subtype.ext
      simp [Port3_FlushInstall.fromSlice,Slice.setAtNat,List.map_set]
    · exact ih s

theorem slice_roundtrip (s : Slice K) :
    Port3_FlushInstall.fromSlice (S8Kani2FinishReferenceJoin.toSlice (Port3_FlushInstall.toWeights s)) = s := by
  apply Subtype.ext
  simp only [Port3_FlushInstall.fromSlice,S8Kani2FinishReferenceJoin.toSlice,
    Port3_FlushInstall.toWeights,List.map_map]
  have id : (fun x : K => Port3_FlushInstall.fromMutable
      (S8Kani2FinishReferenceJoin.toFinish (Port3_FlushInstall.toOwned x))) = (fun x => x) := by
    funext x
    cases x with | mk c0 c1 => cases c0; cases c1; rfl
  change List.map (fun x : K => Port3_FlushInstall.fromMutable (S8Kani2FinishReferenceJoin.toFinish (Port3_FlushInstall.toOwned x))) s.val = s.val
  rw [id,List.map_id]

/-- Current deferred mutable ABI agrees as a complete Result with retained S8.
The value child is explicitly the retained reducer interpretation, not an
unproved assertion about a different native arithmetic extraction. -/
theorem reference_eq (self : verifier.BatchedWeights) (old : Slice K)
    (lengths : old.val.length ≤ self.raw.val.length) :
    Port3_NativeFlushBody.verifier.BatchedWeights.finish std value self old =
      Port3_FlushInstall.flush self old := by
  let bw : S8Kani2MutableValue.F.BW := ⟨self.raw,self.terms⟩
  let f := S8Kani2MutableValue.valueAt bw
  have hv : ∀ i : Usize, i.val < old.val.length → value self i = ok (Port3_FlushInstall.fromMutable (f i.val)) := by
    intro i hi
    change (do let q ← S8Kani2MutableValue.F.value bw i; ok (Port3_FlushInstall.fromMutable q)) = _
    rw [S8Kani2MutableValue.valueAt_success bw i (by change i.val < self.raw.val.length; omega)]
    rfl
  rw [finish_total self value old (fun j => Port3_FlushInstall.fromMutable (f j)) hv]
  obtain ⟨out,run,shape⟩ := S8Kani2MutableExtraction.batched_weights.finish_output_invariant
    bw (S8Kani2FinishReferenceJoin.toSlice (Port3_FlushInstall.toWeights old)) f
    (by intro i hi; exact S8Kani2MutableValue.valueAt_success bw i (by
          change i.val < self.raw.val.length
          change i.val < old.val.length at hi
          omega))
  simp only [Port3_FlushInstall.flush,run,bind_tc_ok]
  rw [shape,prefix_transport,slice_roundtrip]
  rfl

/-- Actual stage Vec deref_mut/back-write ABI; every non-weight field is
preserved by the caller's materialization. -/
def finishVec (self : verifier.BatchedWeights) (weights : alloc.vec.Vec K) : Result (alloc.vec.Vec K) := do
  let (s,back) ← lift (alloc.vec.Vec.deref_mut weights)
  let out ← Port3_NativeFlushBody.verifier.BatchedWeights.finish std value self s
  ok (back out)

theorem vec_backwrite (self : verifier.BatchedWeights) (weights : alloc.vec.Vec K)
    (lengths : weights.val.length ≤ self.raw.val.length) :
    finishVec self weights = (do let out ← Port3_FlushInstall.flush self weights.deref; ok ⟨out.val,out.property⟩) := by
  simp only [finishVec,alloc.vec.Vec.deref_mut,lift,bind_tc_ok]
  change (do let out ← Port3_NativeFlushBody.verifier.BatchedWeights.finish std value self weights.deref; ok (⟨out.val,out.property⟩ : alloc.vec.Vec K)) = _
  rw [reference_eq self weights.deref lengths]
  rfl

#print axioms finish_total
#print axioms prefix_transport
#print axioms slice_roundtrip
#print axioms reference_eq
#print axioms vec_backwrite
end AspisR1.Port4D_FlushABI
end
