import JGj_DotChunkSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_DotChunkTotal
open Aeneas Aeneas.Std Result FIq_Native
open FJb_TailCell (cell)
open JGj_DotInput (Budget)
open JGj_DotChunkSource (Range Raw4)
def WCanonical (w : Slice field.QM31) : Prop := ∀ x∈w.val,FIv_NativeValue.Canon x
def VCanonical (v : Slice U32) : Prop := ∀ x∈v.val,x.val<AspisV8R17.RawReducer.P
theorem source (fuel : Nat) (iter : Range) (weights : Slice field.QM31) (values : Slice U32)
    (raw : Raw4) (n : Nat) (hwEnd : iter.end.val≤weights.val.length) (hvEnd : iter.end.val≤values.val.length)
    (hspan : iter.start.val+fuel=iter.end.val) (hcount : n+fuel≤4)
    (hw : WCanonical weights) (hv : VCanonical values) (hb : Budget raw n) :
    ∃ out,field.qm31_m31_dot_loop1_loop0 iter weights values raw=ok out ∧ Budget out (n+fuel) := by
  induction fuel generalizing iter raw n with
  | zero =>
    refine ⟨raw,?_,by simpa only [Nat.add_zero] using hb⟩
    rw [JGj_DotChunkSource.source_loop_eq,OccupancyRangeTraversal.next_done iter (by omega)]
    rfl
  | succ fuel ih =>
    have hwidx : iter.start.val<weights.val.length := by omega
    have hvidx : iter.start.val<values.val.length := by omega
    let q := weights.val[iter.start.val]'hwidx
    let v := values.val[iter.start.val]'hvidx
    have rq : Slice.index_usize weights iter.start=ok q := by
      simp only [Slice.index_usize,List.getElem?_eq_getElem hwidx,q]
    have rv : Slice.index_usize values iter.start=ok v := by
      simp only [Slice.index_usize,List.getElem?_eq_getElem hvidx,v]
    obtain ⟨nextRaw,ri,bi,_⟩ := JGj_DotInput.source_success raw q v n (by omega) hb
      (hw q (List.getElem_mem _)) (hv v (List.getElem_mem _))
    obtain ⟨iter1,rnext,vstart,vend,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨out,ro,bo⟩ := ih iter1 nextRaw (n+1) (by rw [vend];exact hwEnd)
      (by rw [vend];exact hvEnd) (by rw [vend,vstart];omega) (by omega) bi
    have he : n+1+fuel=n+(fuel+1) := by omega
    rw [he] at bo
    refine ⟨out,?_,bo⟩
    rw [JGj_DotChunkSource.source_loop_eq,rnext]
    change (do
      let value ← Slice.index_usize values iter.start
      let weight ← Slice.index_usize weights iter.start
      let next ← JGj_DotInput.run raw weight value
      field.qm31_m31_dot_loop1_loop0 iter1 weights values next)=ok out
    rw [rv,bind_tc_ok,rq,bind_tc_ok,ri,bind_tc_ok,ro]
#print axioms source
end AspisR1.JGj_DotChunkTotal
end
