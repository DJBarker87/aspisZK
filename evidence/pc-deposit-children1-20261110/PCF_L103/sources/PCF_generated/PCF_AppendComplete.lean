import PCF_AppendLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_AppendComplete
open PCF_AppendStep PCF_AppendLoop

theorem complete (header : PCB_AppendFullRef.RootPageHeaderV1) (roots : Slice Root) (initial : Slice U8)
    (capacity : header.filled.val+roots.length ≤ 256)
    (extent : 64+32*(header.filled.val+roots.length) ≤ initial.length) :
    ∃ (out : Slice U8) (filled : U16),
      PCB_AppendFullRef.append_ref initial header roots = ok out ∧
      filled.val=header.filled.val+roots.length ∧ out.length=initial.length ∧
      PCF_SliceFrame.view out = PCB_AppendFrame.finish
        (fun k => (core.num.U16.to_le_bytes filled).val[k-56]!)
        (PCB_AppendFrame.run (rootBytes roots) (PCF_SliceFrame.view initial) header.filled.val roots.length) := by
  obtain ⟨⟨current,header'⟩,hloop,hheader,hlen,hview⟩ := PCF_AppendLoop.loop header roots initial capacity extent
  change header'=header at hheader
  subst header'
  change current.length=initial.length at hlen
  let count := UScalar.cast .U16 (Slice.len roots)
  have vc : count.val=roots.length := by dsimp [count]; scalar_tac
  obtain ⟨filled,hfilled,vfilled⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x:=header.filled) (y:=count) (by scalar_tac))
  let out := current.setSlice! 56 (core.num.U16.to_le_bytes filled).val
  have hbytes : (core.num.U16.to_le_bytes filled).val.length=2 := (core.num.U16.to_le_bytes filled).property
  have hbounds : (56#usize) ≤ 58#usize ∧ (58#usize).val ≤ current.length := by scalar_tac
  have hwidth : (Array.to_slice (core.num.U16.to_le_bytes filled)).length = (58#usize).val-(56#usize).val := by exact hbytes
  have hcopy := PCF_CopyRange.result current (Array.to_slice (core.num.U16.to_le_bytes filled))
    {start:=56#usize,«end»:=58#usize} hbounds hwidth
  refine ⟨out,filled,?_,by scalar_tac,?_,?_⟩
  · simp only [PCB_AppendFullRef.append_ref,core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.enumerate.trait_default,bind_tc_ok]
    change (do let (data1,header1) ← PCB_AppendFullRef.append_ref_loop (PCF_Iterator.cursor roots 0 0#usize) initial header
               let filled ← header1.filled+count
               let (window,back) ← core.slice.index.SliceIndexRangeUsizeSlice.index_mut {start:=56#usize,«end»:=58#usize} data1
               let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window (Array.to_slice (core.num.U16.to_le_bytes filled))
               ok (back copied)) = _
    rw [hloop]; simp only [bind_tc_ok]
    change (do let filled ← header.filled+count
               let (window,back) ← core.slice.index.SliceIndexRangeUsizeSlice.index_mut {start:=56#usize,«end»:=58#usize} current
               let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window (Array.to_slice (core.num.U16.to_le_bytes filled))
               ok (back copied)) = _
    rw [hfilled]; simp only [bind_tc_ok]
    exact hcopy
  · exact (PCF_SliceFrame.length current 56 _).trans hlen
  · unfold out
    rw [PCF_SliceFrame.window current 56 _ (by scalar_tac)]
    rw [hbytes,hview]
    rfl

#print axioms complete
end PCF_AppendComplete
