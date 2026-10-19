import AspisR1RhoHeap.Funs
import CuSavingsRhoInitSource

/-! Discharge the initializer's length premise from the whole actual heap
helper. No reserve-success or reserve-frame premise is needed: every successful
helper result passes through the original runtime resize operation.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoHeap
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoPushStep

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem resize_length {T : Type} (clone : core.clone.Clone T) (input out : alloc.vec.Vec T)
    (length : Usize) (value : T)
    (h : Aeneas.Std.alloc.vec.Vec.resize clone input length value = .ok out) :
    out.val.length = length.val := by
  unfold Aeneas.Std.alloc.vec.Vec.resize at h
  split at h
  · cases Result.ok.inj h
    exact List.length_resize
  · obtain ⟨_,_,h⟩ := bind_ok _ _ _ h
    cases Result.ok.inj h
    exact List.length_resize

variable [HeapReserve]

theorem source_length {T : Type} (copy : core.marker.Copy T) (length : Usize)
    (value : T) (out : alloc.vec.Vec T)
    (h : r0.heap.source_filled copy length value = .ok (.Ok out)) :
    out.val.length = length.val := by
  unfold r0.heap.source_filled at h
  obtain ⟨pair,_,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨reserve,input⟩
  simp only [uncurry_apply_pair] at h
  cases reserve with
  | Err error =>
    simp only [core.result.Result.map_err,AspisR1PublicPreparation.core.result.Result.map_err,
      r0.heap.source_filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError,
      r0.heap.source_filled.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError.call_once,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    cases h
  | Ok unit =>
    simp only [core.result.Result.map_err,AspisR1PublicPreparation.core.result.Result.map_err,
      bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨resized,hresize,h⟩ := bind_ok _ _ _ h
    have heq := core.result.Result.Ok.inj (Result.ok.inj h)
    exact heq ▸ resize_length copy.cloneInst input resized length value hresize

def sourceAllocator : InitAllocation where
  filled := @r0.heap.source_filled _

theorem initializer_outcome (weights : Slice field.QM31) :
    @CuSavingsRhoInitSource.sourceNew sourceAllocator weights =
      (do let result ← @CuSavingsRhoInitSource.heapResult sourceAllocator weights
          .ok (CuSavingsRhoInitSource.heapOutcome weights result)) := by
  letI : InitAllocation := sourceAllocator
  apply CuSavingsRhoInitSource.source_outcome weights
  intro raw h
  change r0.heap.source_filled
    (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) (Slice.len weights)
    (Array.repeat 4#usize 0#u64) = .ok (.Ok raw) at h
  have hl := source_length _ _ _ raw h
  exact hl.trans (by simpa only [Slice.length] using Slice.len_val weights)

#print axioms resize_length
#print axioms source_length
#print axioms initializer_outcome
end AspisR1.CuSavingsRhoHeap
