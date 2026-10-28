import R1Z.BuilderBankRange
import R1Z.BuilderStdCollect
import R1Z.BuilderRecordsFields

/-! A successful mapped range collection has the exact range length even
when the mapper is partial. No totality of the cryptographic callee is assumed. -/
set_option autoImplicit false
namespace R1Z.BuilderBankCollect
open Aeneas Aeneas.Std Result BuilderStdModels BuilderRecordsFields
variable {C T : Type}
abbrev Range := core.ops.range.Range Usize
abbrev MapRange (C : Type) := core.iter.adapters.map.Map Range C

def mapped (f : core.ops.function.FnMut C Usize T) :
    core.iter.traits.iterator.Iterator (MapRange C) T :=
  mappedIterator (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) f

theorem collect_length (f : core.ops.function.FnMut C Usize T)
    (r : Range) (c : C) (acc out : List T)
    (hbound : r.start.val ≤ r.end.val)
    (h : alloc.vec.FromIteratorVec.iterToList (mapped f) ⟨r,c⟩ acc = ok out) :
    out.length = acc.length + (r.end.val-r.start.val) := by
  generalize he : r.end.val-r.start.val = remaining
  induction remaining using Nat.strong_induction_on generalizing r c acc out with
  | h remaining ih =>
    rw [alloc.vec.FromIteratorVec.iterToList] at h
    by_cases hlt : r.start.val < r.end.val
    · obtain ⟨after,hn,hs,he'⟩ := BuilderBankRange.next_some r hlt
      have hm : (mapped f).next ⟨r,c⟩ = (do
          let (v,c') ← f.call_mut c r.start
          ok (some v,⟨after,c'⟩)) := by
        change mapNext _ f ⟨r,c⟩ = _
        rw [mapNext]
        simp only [core.iter.traits.iterator.IteratorRange]
        rw [hn]; rfl
      rw [hm] at h
      obtain ⟨⟨v,c'⟩,_,h⟩ := bind_ok_inv (by simpa only [bind_assoc_eq,bind_tc_ok] using h)
      have ht := ih (after.end.val-after.start.val) (by rw [he']; omega)
        after c' (v::acc) out (by rw [he']; omega) h rfl
      simp only [List.length_cons] at ht
      rw [he'] at ht
      omega
    · have hn := BuilderBankRange.next_none r (by omega)
      have hm : (mapped f).next ⟨r,c⟩ = ok (none,⟨r,c⟩) := by
        change mapNext _ f ⟨r,c⟩ = _
        rw [mapNext]
        simp only [core.iter.traits.iterator.IteratorRange]
        rw [hn]; rfl
      rw [hm] at h
      simp only [bind_tc_ok] at h
      have hout : out = acc.reverse := (Result.ok.inj h).symm
      rw [hout,List.length_reverse]
      omega

theorem vector_length (f : core.ops.function.FnMut C Usize T)
    (r : Range) (c : C) (out : alloc.vec.Vec T) (hbound : r.start.val ≤ r.end.val)
    (h : core.iter.traits.iterator.Iterator.collect.default (mapped f)
      (core.iter.traits.collect.FromIteratorVec T) ⟨r,c⟩ = ok out) :
    out.val.length = r.end.val-r.start.val := by
  unfold core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.collect.FromIteratorVec alloc.vec.FromIteratorVec.from_iter at h
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter,bind_tc_ok] at h
  obtain ⟨xs,hxs,h⟩ := bind_ok_inv h
  by_cases hb : xs.length ≤ Usize.max
  · rw [dif_pos hb] at h
    have ho := congrArg Subtype.val (Result.ok.inj h)
    rw [← ho]
    simpa using collect_length f r c [] xs hbound hxs
  · rw [dif_neg hb] at h
    cases h

theorem parts_blocks_length
    (w : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RW)
    (p : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.RP)
    (pt : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.Parts)
    (h : AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.parts w p = ok pt) :
    pt.blocks.val.length = 57 := by
  unfold AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.parts at h
  simp only [AspisBuilderGlueSource.core.iter.traits.iterator.Iterator.map.default,
    iterMap,bind_tc_ok] at h
  obtain ⟨blocks,hblocks,h⟩ := bind_ok_inv h
  have hlen := vector_length
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256
    ⟨0#usize,57#usize⟩ (w,p) blocks (by simp) hblocks
  obtain ⟨⟨cur,l,r⟩,_,h⟩ := bind_ok_inv h
  obtain ⟨path,_,h⟩ := bind_ok_inv h
  obtain ⟨inRec,_,h⟩ := bind_ok_inv h
  obtain ⟨outRec,_,h⟩ := bind_ok_inv h
  obtain ⟨aux,_,h⟩ := bind_ok_inv h
  have hp := congrArg
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.Parts.blocks (Result.ok.inj h)
  rw [← hp]
  simpa using hlen

#print axioms collect_length
#print axioms vector_length
#print axioms parts_blocks_length
end R1Z.BuilderBankCollect
