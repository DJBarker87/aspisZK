import R1Z.BuilderBlockResult
import R1Z.BuilderBankCollect

/-! Order-preserving collection of the actual 57 block calls. -/
set_option autoImplicit false
namespace R1Z.BuilderBlockCollect
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderStdModels BuilderRecordsFields
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder
abbrev Range := core.ops.range.Range Usize

theorem mapped_trace_bounded {C T : Type} (f : core.ops.function.FnMut C Usize T)
    (g : Nat → T) (c : C) (r : Range) (hbound : r.start.val ≤ r.end.val)
    (hend : r.end.val ≤ 57)
    (hf : ∀ i, i.val < 57 → f.call_mut c i = ok (g i.val,c)) :
    FiniteTrace (BuilderBankCollect.mapped f) ⟨r,c⟩
      ((List.range' r.start.val (r.end.val-r.start.val)).map g) := by
  generalize he : r.end.val-r.start.val = remaining
  induction remaining using Nat.strong_induction_on generalizing r with
  | h remaining ih =>
    by_cases hlt : r.start.val < r.end.val
    · obtain ⟨after,hn,hs,he'⟩ := BuilderBankRange.next_some r hlt
      have ht := ih (after.end.val-after.start.val) (by rw [he'];omega) after
        (by rw [he'];omega) (by rw [he'];exact hend) rfl
      have hm : (BuilderBankCollect.mapped f).next ⟨r,c⟩ = ok (some (g r.start.val),⟨after,c⟩) := by
        change mapNext _ f ⟨r,c⟩ = _
        rw [mapNext]
        simp only [core.iter.traits.iterator.IteratorRange]
        rw [hn]
        simp only [bind_tc_ok]
        rw [hf r.start (by omega)]
        rfl
      have hlen : remaining = (after.end.val-after.start.val)+1 := by rw [he'] at *;omega
      rw [hlen,List.range'_succ,List.map_cons]
      have hs' : after.start.val = r.start.val+1 := hs
      rw [← hs']
      exact .step _ _ _ _ hm ht
    · have hn := BuilderBankRange.next_none r (by omega)
      have hm : (BuilderBankCollect.mapped f).next ⟨r,c⟩ = ok (none,⟨r,c⟩) := by
        change mapNext _ f ⟨r,c⟩ = _
        rw [mapNext]
        simp only [core.iter.traits.iterator.IteratorRange]
        rw [hn];rfl
      have hz : remaining = 0 := by omega
      rw [hz]
      exact .done _ _ hm

theorem vector_values {C T : Type} [Inhabited T] (f : core.ops.function.FnMut C Usize T)
    (g : Nat → T) (c : C)
    (hf : ∀ i, i.val < 57 → f.call_mut c i = ok (g i.val,c)) :
    ∃ out, core.iter.traits.iterator.Iterator.collect.default (BuilderBankCollect.mapped f)
      (core.iter.traits.collect.FromIteratorVec T) ⟨⟨0#usize,57#usize⟩,c⟩ = ok out ∧
      ∀ j, j < 57 → out.val[j]! = g j := by
  have ht := mapped_trace_bounded f g c ⟨0#usize,57#usize⟩ (by simp) (by simp) hf
  have hc := collect_trace _ _ _ ht []
  simp only [List.reverse_nil,List.nil_append,UScalar.ofNatCore_val_eq,Nat.sub_zero] at hc
  have hlen : ((List.range' 0 57).map g).length ≤ Usize.max := by
    simp only [List.length_map,List.length_range']
    scalar_tac
  unfold core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.collect.FromIteratorVec alloc.vec.FromIteratorVec.from_iter
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter,bind_tc_ok]
  rw [hc]
  simp only [bind_tc_ok]
  rw [dif_pos hlen]
  refine ⟨_,rfl,?_⟩
  intro j hj
  simp [List.getElem!_eq_getElem?_getD,hj]

theorem parts_blocks (w : RW) (p : RP) (pt : Parts) (h : parts w p = ok pt) :
    ∀ j, j < 57 → pt.blocks.val[j]! = blockR (BuilderPrimitiveArguments.wordWitness w)
      (BuilderPrimitiveArguments.wordPublic p) j := by
  let f := parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256
  let g := blockR (BuilderPrimitiveArguments.wordWitness w) (BuilderPrimitiveArguments.wordPublic p)
  have hf : ∀ i : Usize, i.val < 57 → f.call_mut (w,p) i = ok (g i.val,(w,p)) := by
    intro i hi
    change parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256.call_mut (w,p) i = _
    rw [parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU32256.call_mut,
      BuilderBlockResult.writer_ok w p i hi]
    rfl
  obtain ⟨blocks,hblocks,hvalues⟩ := vector_values f g (w,p) hf
  unfold parts at h
  simp only [AspisBuilderGlueSource.core.iter.traits.iterator.Iterator.map.default,iterMap,bind_tc_ok] at h
  change (do let blocks ← core.iter.traits.iterator.Iterator.collect.default (BuilderBankCollect.mapped f)
                (core.iter.traits.collect.FromIteratorVec (Array U32 256#usize)) ⟨⟨0#usize,57#usize⟩,(w,p)⟩
             _) = ok pt at h
  rw [hblocks] at h
  simp only [bind_tc_ok] at h
  obtain ⟨⟨cur,l,r⟩,_,h⟩ := bind_ok_inv h
  obtain ⟨path,_,h⟩ := bind_ok_inv h
  obtain ⟨input,_,h⟩ := bind_ok_inv h
  obtain ⟨output,_,h⟩ := bind_ok_inv h
  obtain ⟨aux,_,h⟩ := bind_ok_inv h
  have he := congrArg Parts.blocks (Result.ok.inj h)
  intro j hj
  rw [← he]
  exact hvalues j hj

#print axioms mapped_trace_bounded
#print axioms vector_values
#print axioms parts_blocks
end R1Z.BuilderBlockCollect
