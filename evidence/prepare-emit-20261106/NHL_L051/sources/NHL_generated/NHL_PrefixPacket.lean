import NHL_PrepareModel
import NHL_BorrowWindows
import NHL_SplitPacket
import NHL_HeapPacket
import NHL_ValuesPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PrefixPacket
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_PrepareStages NGV_ByteWindow

theorem rejected (base : Ops) {H : Type} (D : aspis_core.digest.Digest32 H) (proof : Slice U8) :
 buffers (NHL_Packets.installed base false) D proof=ok (.Err .Allocation) := by
 obtain ⟨_,_,_,ly,ls,add,_,_⟩ := ConcreteConstants.constants_total (NHL_Packets.installed base false)
 rw [NHL_PrepareModel.source_constants] at ls
 unfold buffers
 simp only [ls,ly,bind_tc_ok]
 rw [NHL_PrepareEq.logical_add base,add,bind_tc_ok]
 change (do
   let r ← NHL_Packets.filled false core.marker.CopyU8 14759#usize 0#u8
   _) = _
 rw [NHL_HeapPacket.rejected,bind_tc_ok]
 rfl

/-- Allocation, actual split, both expansions, back-functions and subsequent
borrows are composed on the SAME records. The final full View Result remains
arbitrary; noncanonical inactive input is allowed and rejected by the view. -/
theorem accepted (base : Ops) {H : Type} (D : aspis_core.digest.Digest32 H) (proof : Slice U8)
 (proofSize : proof.val.length=57607) :
 ∃ semantic y1 : Slice U8, semantic.val.length=13831 ∧ y1.val.length=928 ∧
 buffers (NHL_Packets.installed base true) D proof=InstalledPreparation.sourceView proof semantic y1 := by
 obtain ⟨logical,heap,logicalSize⟩ := NHL_HeapPacket.accepted
 obtain ⟨parts,semantic,y1,splitRun,semRun,yRun,semSize,ySize,back,view⟩ :=
   NHF_Prefix.construct proof logical proofSize logicalSize
 rcases parts with ⟨⟨s0,y0⟩,rejoin⟩
 let parts := ((s0,y0),rejoin)
 obtain ⟨leftSize,rightSize⟩ := NHL_SplitPacket.sizes logical parts logicalSize splitRun
 have left : semantic.length=parts.1.1.length := semSize.trans leftSize.symm
 have right : y1.length=parts.1.2.length := ySize.trans rightSize.symm
 have windows := NHF_Recombine.windows logical (alloc.vec.Vec.deref_mut logical) parts semantic y1
   rfl splitRun left right semSize ySize
 let vector := (alloc.vec.Vec.deref_mut logical).2 (parts.2 (semantic,y1))
 have vectorSize : vector.val.length=14759 := windows.2.2
 have first := NHL_BorrowWindows.left vector semantic 13831#usize (by change 13831≤vector.val.length;omega) windows.1
 have second := NHL_BorrowWindows.right vector y1 13831#usize (by change 13831≤vector.val.length;omega) windows.2.1
 have semRange := NGV_ByteWindow.read proof 16#usize 7031#usize (by change 16≤7031 ∧ 7031≤proof.val.length; omega)
 have yRange := NGV_ByteWindow.read proof 7031#usize 7495#usize (by change 7031≤7495 ∧ 7495≤proof.val.length; omega)
 change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proof {start:=16#usize,«end»:=7031#usize}=ok (select proof 16 7015) at semRange
 change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proof {start:=7031#usize,«end»:=7495#usize}=ok (select proof 7031 464) at yRange
 have values := NHL_ValuesPacket.accepted _ _ _ yRun
 obtain ⟨offset,y1off,inactive,ly,ls,add,_,_⟩ := ConcreteConstants.constants_total (NHL_Packets.installed base true)
 rw [NHL_PrepareModel.source_constants] at y1off inactive ls
 refine ⟨semantic,y1,semSize,ySize,?_⟩
 unfold buffers
 simp only [ls,ly,bind_tc_ok]
 rw [NHL_PrepareEq.logical_add base,add,bind_tc_ok]
 have heapCall : (NHL_Packets.installed base true).op1 core.marker.CopyU8 14759#usize 0#u8=ok (.Ok logical) := heap
 rw [heapCall,bind_tc_ok]
 simp only [AspisR1CurrentCaller.core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
   lift,Aeneas.Std.uncurry]
 rw [splitRun,bind_tc_ok]
 dsimp! only
 rw [y1off,bind_tc_ok,semRange,bind_tc_ok]
 have semanticCall : (NHL_Packets.installed base true).op10 (select proof 16 7015) parts.1.1=ok (.Ok (),semantic) := semRun
 rw [semanticCall,bind_tc_ok]
 dsimp! only
 try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
 rw [inactive,bind_tc_ok,yRange,bind_tc_ok]
 have valuesCall : (NHL_Packets.installed base true).op11 (select proof 7031 464) parts.1.2=ok (.Ok (),y1) := values
 rw [valuesCall,bind_tc_ok]
 dsimp! only
 try simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
 rw [first,bind_tc_ok,second,bind_tc_ok]
 change (do let r ← InstalledPreparation.sourceView proof semantic y1; ok r)=_
 rw [view,bind_tc_ok]
#print axioms rejected
#print axioms accepted
end AspisR1.NHL_PrefixPacket
