import BatchedWeightsPushLoopAllPrefixV11
import BatchedWeightsFlushLaneV8
import BatchedWeightsFlushLaneBindV3
import AspisR1BatchedUsizeFlushBridgePublic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace BatchedWeightsPushOuterFlushV13
open AspisR1BatchedWeightsExtraction
open AspisR1BatchedWeightsPushLoopAllPrefixV11
open BatchedWeightsFlushLaneV8
abbrev BW := batched_weights.BatchedWeights
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31
abbrev Range := core.ops.range.Range Usize

/-- Successful outer generated `push`, including its actual four-lane fold
branch.  The raw lane values are exposed through the flush helper; terms is
unchanged because the caller increments once after all selected pushes. -/
theorem push_flush_success
    (index : Usize) (initial : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hflush : initial.terms.val % 4 = 3) :
    ∃ mid : BW, ∃ lane newLane : Array Std.U64 4#usize,
      ∃ old : Array Std.U64 4#usize,
      ∃ back : Array Std.U64 4#usize → alloc.vec.Vec (Array Std.U64 4#usize),
      batched_weights.BatchedWeights.push_loop
        ({ start := 0#usize, «end» := 4#usize } : Range)
        initial index basis
        (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) = .ok mid ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (Array Std.U64 4#usize)) mid.raw index = .ok lane ∧
      BatchedWeightsFlushLaneV8.flushLane lane = .ok newLane ∧
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        (Array Std.U64 4#usize)) mid.raw index = .ok (old, back) ∧
      batched_weights.BatchedWeights.push initial index power basis =
        .ok { mid with raw := back newLane } ∧
      mid.terms = initial.terms := by
  obtain ⟨mid,hloop,hpost⟩ := push_loop_all_prefix index initial power basis
    hindex hraw ha hb hc hd hbasis
  have hmidTerms : mid.terms = initial.terms := hpost.1
  have hmidIndex : index.val < mid.raw.length := hpost.2.1
  obtain ⟨lane,hvec,hvalue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec mid.raw index hmidIndex)
  have hvec' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      (Array Std.U64 4#usize)) mid.raw index = .ok lane := by
    rw [alloc.vec.Vec.index_slice_index]
    exact hvec
  have hbound0 : (0#usize).val < lane.length := by
    simpa [lane.property]
  have hbound1 : (1#usize).val < lane.length := by
    simpa [lane.property]
  have hbound2 : (2#usize).val < lane.length := by
    simpa [lane.property]
  have hbound3 : (3#usize).val < lane.length := by
    simpa [lane.property]
  obtain ⟨x0,h0,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 0#usize hbound0)
  obtain ⟨x1,h1,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 1#usize hbound1)
  obtain ⟨x2,h2,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 2#usize hbound2)
  obtain ⟨x3,h3,_⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 3#usize hbound3)
  obtain ⟨newLane,y0,y1,y2,y3,hflushLane,hy0,hy1,hy2,hy3,
      hy0out,hy1out,hy2out,hy3out,hv0,hv1,hv2,hv3⟩ :=
    flushLane_coordinates lane x0 x1 x2 x3 h0 h1 h2 h3
  let back : Array Std.U64 4#usize → alloc.vec.Vec (Array Std.U64 4#usize) :=
    alloc.vec.Vec.set mid.raw index
  have hmut : alloc.vec.Vec.index_mut_usize mid.raw index = .ok (lane, back) := by
    simp only [alloc.vec.Vec.index_mut_usize, hvec]
    rfl
  have hmut' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      (Array Std.U64 4#usize)) mid.raw index = .ok (lane, back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  have hcond : mid.terms &&& 3#usize = 3#usize := by
    apply UScalar.eq_of_val_eq
    have htest : (UScalar.and mid.terms (3#usize)).val = 3 := by
      have h0' := (AspisR1BatchedUsizeFlushBridgePublic.source_usize_flush_test_iff
        initial.terms).2 hflush
      rw [← hmidTerms] at h0'
      exact h0'
    calc
      (mid.terms &&& 3#usize).val =
          mid.terms.val &&& (3#usize).val := UScalar.val_and _ _
      _ = (UScalar.and mid.terms (3#usize)).val := (UScalar.val_and _ _).symm
      _ = 3 := htest
  refine ⟨mid,lane,newLane,lane,back,hloop,hvec',hflushLane,hmut',?_,hmidTerms⟩
  let k : Array Std.U64 4#usize → Result BW := fun out => do
    let (_, back') ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      (Array Std.U64 4#usize)) mid.raw index
    ok { mid with raw := back' out }
  simp only [batched_weights.BatchedWeights.push, hloop, bind_tc_ok,
    hcond, if_pos, hvec', bind_tc_ok]
  change (do
      let i5 ← Array.index_usize lane 0#usize
      let i6 ← lift (i5 &&& 2147483647#u64)
      let i7 ← i5 >>> 31#i32
      let i8 ← i6 + i7
      let i9 ← Array.index_usize lane 1#usize
      let i10 ← lift (i9 &&& 2147483647#u64)
      let i11 ← i9 >>> 31#i32
      let i12 ← i10 + i11
      let i13 ← Array.index_usize lane 2#usize
      let i14 ← lift (i13 &&& 2147483647#u64)
      let i15 ← i13 >>> 31#i32
      let i16 ← i14 + i15
      let i17 ← Array.index_usize lane 3#usize
      let i18 ← lift (i17 &&& 2147483647#u64)
      let i19 ← i17 >>> 31#i32
      let i20 ← i18 + i19
      k (Array.make 4#usize [i8,i12,i16,i20])) = .ok { mid with raw := back newLane }
  rw [BatchedWeightsFlushLaneBindV1.flushLane_bind lane k]
  simp only [hflushLane, k, hmut', bind_tc_ok]
  rfl

#print axioms push_flush_success
end BatchedWeightsPushOuterFlushV13
