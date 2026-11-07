import PCF_Iterator
import PCF_DigestShape
import PCF_CopyMap
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace PCF_AppendStep
abbrev Root := Array U32 8#usize
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Root)

theorem live (header : PCB_AppendFullRef.RootPageHeaderV1)
    (roots : Slice Root) (i : Nat) (count : Usize) (data : Slice U8)
    (count_eq : count.val = i) (live : i < roots.length)
    (capacity : header.filled.val + roots.length ≤ 256)
    (extent : 64+32*(header.filled.val+roots.length) ≤ data.length) :
    ∃ count' start : Usize, count'.val = i+1 ∧
      start.val = 64+32*(header.filled.val+i) ∧
      PCB_AppendFullRef.append_ref_loop.body header (PCF_Iterator.cursor roots i count) data =
        ok (cont (PCF_Iterator.cursor roots (i+1) count',
          data.setSlice! start.val (AspisR1.S2K.DigestBytes.bytes roots[i]).val)) := by
  obtain ⟨count',vc',hit⟩ := PCF_Iterator.step roots i count live (by scalar_tac)
  let idx := core.convert.num.FromUsizeU16.from header.filled
  have vidx : idx.val = header.filled.val := core.convert.num.FromUsizeU16.from_val_eq _
  obtain ⟨slot,hs,vs⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=idx) (y:=count) (by scalar_tac))
  obtain ⟨mul,hm,vm⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=slot) (y:=32#usize) (by scalar_tac))
  obtain ⟨start,hstart,vstart⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=64#usize) (y:=mul) (by scalar_tac))
  obtain ⟨last,hlast,vlast⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=start) (y:=32#usize) (by scalar_tac))
  refine ⟨count',start,by scalar_tac,by scalar_tac,?_⟩
  simp only [PCB_AppendFullRef.append_ref_loop.body, hit, bind_tc_ok,
    lift,PCB_AppendFullRef.PAGE_ROOTS_OFFSET]
  change (do let slot ← idx+count
             let mul ← slot*32#usize
             let start ← 64#usize+mul
             let last ← start+32#usize
             let (window,back) ← core.slice.index.SliceIndexRangeUsizeSlice.index_mut
               {start:=start,«end»:=last} data
             let encoded ← PCB_AppendFullRef.encode_digest_canonical roots[i]
             let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window (Array.to_slice encoded)
             ok (cont (PCF_Iterator.cursor roots (i+1) count',back copied))) = _
  rw [hs]; simp only [bind_tc_ok]
  rw [hm]; simp only [bind_tc_ok]
  rw [hstart]; simp only [bind_tc_ok]
  rw [hlast]; simp only [bind_tc_ok]
  rw [PCF_DigestShape.encoder]; simp only [bind_tc_ok]
  apply PCF_CopyMap.result
  · scalar_tac
  · have hlen := (AspisR1.S2K.DigestBytes.bytes roots[i]).property
    change (AspisR1.S2K.DigestBytes.bytes roots[i]).val.length = last.val-start.val
    scalar_tac

#print axioms live
end PCF_AppendStep
