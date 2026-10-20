import CuSavingsRhoBump
import CuSavingsRhoHeapValues
import CuSavingsRhoHeap
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoAllocationSuccess
open Aeneas Aeneas.Std Result AspisR1CuRho AspisR1RhoEmptyReserve
open CuSavingsRhoEmptyReserveModel CuSavingsRhoInitRow CuSavingsRhoPushStep

/- This callback is the concrete Raw4-only empty-buffer allocation projection.
The generic Backend carrier is used only at T = [u64;4]; no layout semantics
are asserted for other T instantiations. Other caller allocations are common
and their future byte budget is retained by source_success below. -/
def raw4Operations (start len : Usize) : RawReserve Usize Unit where
  try_reserve_exact := fun cursor oldLength additional => do
    if oldLength ≠ 0#usize then .fail .panic else do
      if additional = 0#usize then .ok (.Ok (),cursor) else do
        let bytes ← additional*32#usize
        let out ← AspisR1RhoBump.source_alloc start len cursor bytes
        match out with
        | none => .ok (.Err (),cursor)
        | some next => .ok (.Ok (),next)

def raw4Backend (start len cursor : Usize) : Backend where
  ReserveError := Unit
  Buffer := fun _ _ => Usize
  initial := fun _ _ => cursor
  operations := fun _ _ => raw4Operations start len
  nonempty := fun _ _ _ => .fail .panic

theorem reserve_success (start len cursor count : Usize) (future : Nat)
    (h64 : UScalarTy.Usize.numBits=64) (hn : count.val ≤ 256)
    (hfree : start.val+8+32*count.val+7+future ≤ cursor.val) :
    ∃ next,(raw4Operations start len).try_reserve_exact cursor 0#usize count =
      .ok (.Ok (),next) ∧ start.val+8+future ≤ next.val := by
  have hpos : cursor ≠ 0#usize := by
    intro hz
    have hc : cursor.val=0 := by rw [hz];scalar_tac
    omega
  unfold raw4Operations
  simp only [ne_eq,not_true_eq_false,if_false]
  by_cases hz : count=0#usize
  · refine ⟨cursor,?_,by omega⟩
    simp only [hz,if_pos]
  · simp only [hz,if_false]
    have hm : count.val*(32#usize).val ≤ UScalar.max .Usize := by
      have h32 : (32#usize).val=32 := by scalar_tac
      have hlarge : 8192 ≤ UScalar.max .Usize := by scalar_tac
      rw [h32]
      omega
    obtain ⟨bytes,hbytes,hval⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=count) (y:=32#usize) hm)
    have hsize : bytes.val=32*count.val := by
      have h32 : (32#usize).val=32 := by scalar_tac
      rw [h32] at hval
      omega
    obtain ⟨next,hrun,hfuture,_,_⟩ := CuSavingsRhoBump.source_success start len cursor bytes future h64 hpos (by omega)
    refine ⟨next,?_,hfuture⟩
    simp only [hbytes,hrun,bind_tc_ok]

theorem empty_reserve_success (start len cursor count : Usize) (future : Nat)
    (h64 : UScalarTy.Usize.numBits=64) (hn : count.val ≤ 256)
    (hfree : start.val+8+32*count.val+7+future ≤ cursor.val) :
    reserveEmpty (raw4Backend start len cursor) (T:=Raw4) Global count =
      .ok (.Ok (),alloc.vec.Vec.new Raw4) := by
  obtain ⟨next,hrun,_⟩ := reserve_success start len cursor count future h64 hn hfree
  simp only [reserveEmpty,raw4Backend,source_reserve,hrun,bind_tc_ok,uncurry_apply_pair]

private theorem resize_success {T : Type} (clone : core.clone.Clone T)
    (input : alloc.vec.Vec T) (count : Usize) (value : T)
    (hc : clone.clone value = .ok value) :
    ∃ out,alloc.vec.Vec.resize clone input count value = .ok out := by
  unfold alloc.vec.Vec.resize
  split
  · exact ⟨_,rfl⟩
  · rw [hc]
    exact ⟨_,rfl⟩

/-- Whole source heap helper success is derived from the numerical budget,
not supplied as an allocation-success premise. -/
theorem filled_success (start len cursor count : Usize) (future : Nat)
    (h64 : UScalarTy.Usize.numBits=64) (hn : count.val ≤ 256)
    (hfree : start.val+8+32*count.val+7+future ≤ cursor.val)
    (copy : core.marker.Copy Raw4) (value : Raw4)
    (hc : copy.cloneInst.clone value = .ok value) :
    ∃ out,@r0.heap.source_filled (heapReserve (raw4Backend start len cursor)) Raw4 copy count value =
      .ok (.Ok out) := by
  letI : HeapReserve := heapReserve (raw4Backend start len cursor)
  have hr := empty_reserve_success start len cursor count future h64 hn hfree
  change (heapReserve (raw4Backend start len cursor)).reserve Global (alloc.vec.Vec.new Raw4) count =
      .ok (.Ok (),alloc.vec.Vec.new Raw4) at hr
  obtain ⟨out,hresize⟩ := resize_success copy.cloneInst (alloc.vec.Vec.new Raw4) count value hc
  refine ⟨out,?_⟩
  unfold r0.heap.source_filled
  simp only [alloc.vec.Vec.try_reserve_exact,hr,bind_tc_ok,uncurry_apply_pair,
    core.result.Result.map_err,AspisR1PublicPreparation.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,hresize]

/-- Complete actual new/zip initialization succeeds under the concrete raw
residue reservation budget. The zero array clone is the inherited source Copy. -/
theorem initializer_success (start len cursor : Usize) (future : Nat)
    (weights : Slice field.QM31) (h64 : UScalarTy.Usize.numBits=64)
    (hn : weights.val.length ≤ 256)
    (hfree : start.val+8+32*weights.val.length+7+future ≤ cursor.val) :
    @verifier.BatchedWeights.new
      (@CuSavingsRhoHeap.sourceAllocator (heapReserve (raw4Backend start len cursor))) weights =
      .ok (.Ok (initialState weights)) := by
  letI : HeapReserve := heapReserve (raw4Backend start len cursor)
  have hcount : (Slice.len weights).val=weights.val.length := by
    simp only [Slice.len_val,Slice.length]
  obtain ⟨raw,hfill⟩ := filled_success start len cursor (Slice.len weights) future h64
    (by omega) (by omega) (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
    (Array.repeat 4#usize 0#u64) (by rfl)
  letI : InitAllocation := CuSavingsRhoHeap.sourceAllocator
  rw [← CuSavingsRhoInitSource.source_eq,CuSavingsRhoHeap.initializer_outcome]
  change (do
    let result ← r0.heap.source_filled
      (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64) (Slice.len weights)
      (Array.repeat 4#usize 0#u64)
    .ok (CuSavingsRhoInitSource.heapOutcome weights result)) = _
  rw [hfill]
  rfl

#print axioms initializer_success
#print axioms reserve_success
#print axioms empty_reserve_success
#print axioms filled_success
end AspisR1.CuSavingsRhoAllocationSuccess
