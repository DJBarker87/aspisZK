import CuSavingsRhoEmptyReserveModel
import AspisR1RhoHeap.Funs

set_option autoImplicit false
namespace AspisR1.CuSavingsRhoHeapValues
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoEmptyReserveModel

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem resize_values {T : Type} (clone : core.clone.Clone T) (input out : alloc.vec.Vec T)
    (length : Usize) (value : T) (hc : clone.clone value = .ok value)
    (h : alloc.vec.Vec.resize clone input length value = .ok out) :
    out.val=input.val.resize length.val value := by
  unfold alloc.vec.Vec.resize at h
  split at h
  · cases Result.ok.inj h;rfl
  · rw [hc] at h
    simp only [bind_tc_ok] at h
    cases Result.ok.inj h;rfl

/-- Whole actual heap helper: successful filling after reservation of an
empty vector yields exactly the requested repeated value. The raw-buffer
operation remains arbitrary and allocation failure/divergence is retained. -/
theorem source_values (backend : Backend) {T : Type} (copy : core.marker.Copy T)
    (length : Usize) (value : T) (out : alloc.vec.Vec T)
    (hc : copy.cloneInst.clone value = .ok value)
    (h : @r0.heap.source_filled (heapReserve backend) T copy length value = .ok (.Ok out)) :
    out.val=List.replicate length.val value := by
  letI : HeapReserve := heapReserve backend
  change r0.heap.source_filled copy length value = .ok (.Ok out) at h
  unfold r0.heap.source_filled at h
  obtain ⟨pair,hreserve,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨result,input⟩
  change (heapReserve backend).reserve Global (alloc.vec.Vec.new T) length = .ok (result,input) at hreserve
  have hempty := reserve_empty_frame backend T Global length result input hreserve
  subst input
  simp only [uncurry_apply_pair] at h
  cases result with
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
    have hv := resize_values copy.cloneInst (alloc.vec.Vec.new T) resized length value hc hresize
    have hv' : resized.val=List.replicate length.val value := by
      simpa only [alloc.vec.Vec.new,List.resize,Nat.zero_le,ite_true,
        List.take_nil,List.length_nil,Nat.sub_zero,List.nil_append] using hv
    have heq := core.result.Result.Ok.inj (Result.ok.inj h)
    exact heq ▸ hv'

#print axioms resize_values
#print axioms source_values
end AspisR1.CuSavingsRhoHeapValues
