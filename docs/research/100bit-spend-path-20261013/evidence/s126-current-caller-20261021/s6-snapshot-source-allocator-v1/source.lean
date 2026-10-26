import S6BumpReferenceReserveV1
set_option autoImplicit false
namespace AspisS6SnapshotSourceAllocator
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry AspisR1.S2W_D189Wrappers

def word (bytes : Nat) : Usize :=
  UScalar.mk (BitVec.ofNat UScalarTy.Usize.numBits bytes)

theorem word_val (bytes : Nat) (bounded : bytes ≤ Usize.max) : (word bytes).val = bytes := by
  change bytes % 2^UScalarTy.Usize.numBits = bytes
  apply Nat.mod_eq_of_lt
  have ceiling : Usize.max < 2^UScalarTy.Usize.numBits := by decide
  omega

def promote : Option Usize → Result Usize
  | none => fail .panic
  | some cursor => ok cursor

/-- Concrete owned SOURCE reference for the EXISTING private allocator
interface. Snapshot Vec bytes have alignment1; dealloc leaves cursor unchanged.
Not asserted to select the actual native global allocator or entry prefix. -/
def allocator : Allocator Usize where
  allocate := fun cursor bytes =>
    if bytes ≤ Usize.max then do
      let out ← AspisS6BumpOwnedReference.step cursor 0#usize (word bytes) 1#usize
      promote out
    else fail .panic
  cleanup := fun cursor => ok cursor

def requests (sizes : List Nat) : List AspisS6BumpReferenceReserve.WordRequest :=
  sizes.map (fun bytes => (word bytes,1#usize))

/-- Original reservation on the same complete source interface equals the
finite emitted-reference sequence, including panic on ordinary insufficiency. -/
theorem reserve_eq (sizes : List Nat) (cursor : Usize)
    (bounded : ∀ size ∈ sizes, size ≤ Usize.max) :
    AspisR1.S2W_D189Wrappers.reserve allocator sizes cursor =
      (AspisS6BumpReferenceReserve.reserve cursor (requests sizes)).bind promote := by
  induction sizes generalizing cursor with
  | nil => rfl
  | cons size rest ih =>
    have current := bounded size (by simp)
    have tailBounded : ∀ n ∈ rest, n ≤ Usize.max := by
      intro n member
      exact bounded n (by simp [member])
    obtain ⟨out,called,meaning⟩ :=
      AspisS6BumpReferenceExact.step_total_exact cursor 0#usize (word size) 1#usize (by decide)
    cases out with
    | none =>
      simp only [AspisR1.S2W_D189Wrappers.reserve,allocator,current,if_true,
        called,bind_tc_ok,promote,requests,List.map_cons,
        AspisS6BumpReferenceReserve.reserve,AspisR1.S2W_Trace.thenResult,bind_tc_fail]
    | some next =>
      simp only [AspisR1.S2W_D189Wrappers.reserve,allocator,current,if_true,
        called,bind_tc_ok,promote,requests,List.map_cons,
        AspisS6BumpReferenceReserve.reserve,AspisR1.S2W_Trace.thenResult]
      exact ih next tailBounded

theorem admitted_bounds (entry : Entry) :
    ∀ size ∈ admittedSizes entry 3 firstSizes, size ≤ 58295 := by
  by_cases h0 : (entry.buffers (entry.handles 0).1).val.length = 58295
  all_goals by_cases h1 : (entry.buffers (entry.handles 1).1).val.length = 1880
  all_goals by_cases h2 : (entry.buffers (entry.handles 2).1).val.length = 1768
  all_goals simp [admittedSizes,firstSizes,List.range_succ,h0,h1,h2]

theorem snapshot_requests (entry : Entry) :
    AspisS6BumpReferenceReserve.natural (requests (admittedSizes entry 3 firstSizes)) =
      AspisS6AlignedAllocationRange.snapshots entry := by
  unfold AspisS6BumpReferenceReserve.natural requests AspisS6AlignedAllocationRange.snapshots
  rw [List.map_map]
  apply List.map_congr_left
  intro size member
  have bounded : size ≤ Usize.max := by
    have h := admitted_bounds entry size member
    have maxBound : 58295 ≤ Usize.max := by scalar_tac
    omega
  simp only [Function.comp_apply,word_val size bounded]
  rfl

/-- TOTAL original snapshot helper on every COMPLETE Entry. No accepted
caller, buffer validity, alias separation, child success or allocator law is a
premise. Native runtime/caller association and omitted requests remain owed. -/
theorem allocate_snapshots_total (entry : Entry) :
    ∃ next,
      allocateSnapshots allocator entry 3 firstSizes 262144#usize = ok (next,entry.heap) ∧
      200180 ≤ next.val ∧ 200172 ≤ next.val-8 := by
  let sizes := admittedSizes entry 3 firstSizes
  have bounded : ∀ size ∈ sizes, size ≤ Usize.max := by
    intro size member
    have h := admitted_bounds entry size member
    have maxBound : 58295 ≤ Usize.max := by scalar_tac
    omega
  have valid : ∀ request ∈ requests sizes, 0 < request.2.val ∧ request.2.val ≤ 8 := by
    simp [requests]
  have charge : AspisS6AlignedAllocationRange.charge
      (AspisS6BumpReferenceReserve.natural (requests sizes)) ≤ 61964 := by
    rw [snapshot_requests entry]
    exact AspisS6AlignedAllocationRange.snapshot_charge entry
  have fits : 8+AspisS6AlignedAllocationRange.charge
      (AspisS6BumpReferenceReserve.natural (requests sizes)) ≤ (262144#usize).val := by
    change 8+_ ≤ 262144
    omega
  obtain ⟨next,called,header,decreasing,loss⟩ :=
    AspisS6BumpReferenceReserve.reserve_fits (requests sizes) 262144#usize valid fits
  have original : AspisR1.S2W_D189Wrappers.reserve allocator sizes 262144#usize = ok next := by
    rw [reserve_eq sizes 262144#usize bounded,called]
    rfl
  refine ⟨next,?_,?_,?_⟩
  · simp only [allocateSnapshots,original,AspisR1.S2W_Trace.thenResult]
  · change 262144 ≤ next.val+_ at loss
    omega
  · change 262144 ≤ next.val+_ at loss
    omega

#print axioms word_val
#print axioms reserve_eq
#print axioms admitted_bounds
#print axioms snapshot_requests
#print axioms allocate_snapshots_total
end AspisS6SnapshotSourceAllocator
