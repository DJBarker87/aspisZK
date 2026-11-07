import PCF_AppendStep
import PCF_AppendStop
import PCF_SliceFrame
import PCB_AppendFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace PCF_AppendLoop
open PCF_AppendStep

def rootBytes (roots : Slice Root) (row byte : Nat) : U8 :=
  (AspisR1.S2K.DigestBytes.bytes roots.val[row]!).val[byte]!
def Inv (header : PCB_AppendFullRef.RootPageHeaderV1) (roots : Slice Root) (initial : Slice U8)
    (s : Iter × Slice U8) : Prop :=
  ∃ i count, i ≤ roots.length ∧ count.val=i ∧ s.1=PCF_Iterator.cursor roots i count ∧
    s.2.length=initial.length ∧ PCF_SliceFrame.view s.2 =
      PCB_AppendFrame.run (rootBytes roots) (PCF_SliceFrame.view initial) header.filled.val i

theorem loop (header : PCB_AppendFullRef.RootPageHeaderV1) (roots : Slice Root) (initial : Slice U8)
    (capacity : header.filled.val+roots.length ≤ 256)
    (extent : 64+32*(header.filled.val+roots.length) ≤ initial.length) :
    ∃ out, PCB_AppendFullRef.append_ref_loop (PCF_Iterator.cursor roots 0 0#usize) initial header = ok out ∧
      out.2=header ∧ out.1.length=initial.length ∧ PCF_SliceFrame.view out.1 =
        PCB_AppendFrame.run (rootBytes roots) (PCF_SliceFrame.view initial) header.filled.val roots.length := by
  have hp : WP.spec
      (PCB_AppendFullRef.append_ref_loop (PCF_Iterator.cursor roots 0 0#usize) initial header)
      (fun out => out.2=header ∧ out.1.length=initial.length ∧ PCF_SliceFrame.view out.1 =
        PCB_AppendFrame.run (rootBytes roots) (PCF_SliceFrame.view initial) header.filled.val roots.length) := by
    unfold PCB_AppendFullRef.append_ref_loop
    refine loop.spec_decr_nat (fun s : Iter × Slice U8 => roots.length-s.1.iter.i)
      (Inv header roots initial) _
      (fun s => PCB_AppendFullRef.append_ref_loop.body header s.1 s.2)
      (PCF_Iterator.cursor roots 0 0#usize,initial) ?_ ⟨0,0#usize,by omega,rfl,rfl,rfl,rfl⟩
    rintro ⟨iter,current⟩ ⟨i,count,hi,hcount,hiter,hlen,hview⟩
    change iter=PCF_Iterator.cursor roots i count at hiter
    change current.length=initial.length at hlen
    simp only [hiter]
    by_cases more : i < roots.length
    · obtain ⟨count',start,vc,vs,hbody⟩ := PCF_AppendStep.live header roots i count current hcount more capacity (by omega)
      rw [hbody]
      change (Inv header roots initial (PCF_Iterator.cursor roots (i+1) count',
        current.setSlice! start.val (AspisR1.S2K.DigestBytes.bytes roots[i]).val) ∧
        roots.length-(i+1) < roots.length-i)
      refine ⟨⟨i+1,count',by omega,vc,rfl,?_,?_⟩,by omega⟩
      · rw [PCF_SliceFrame.length,hlen]
      · have hbytes : (AspisR1.S2K.DigestBytes.bytes roots[i]).val.length = 32 :=
          (AspisR1.S2K.DigestBytes.bytes roots[i]).property
        rw [PCF_SliceFrame.window current start.val _ (by scalar_tac)]
        rw [hbytes,vs,hview]
        have hroot : roots.val[i]! = roots[i] :=
          List.getElem!_of_getElem? (List.getElem?_eq_getElem more)
        simp only [PCB_AppendFrame.run,PCB_AppendFrame.step,PCB_AppendFrame.base,rootBytes,hroot]
    · have eqi : i=roots.length := by omega
      rw [PCF_AppendStop.stopped header roots i count current (by omega)]
      change header=header ∧ current.length=initial.length ∧ PCF_SliceFrame.view current = _
      exact ⟨rfl,hlen,by simpa only [eqi] using hview⟩
  cases run : PCB_AppendFullRef.append_ref_loop (PCF_Iterator.cursor roots 0 0#usize) initial header with
  | fail e => simp only [run,WP.spec,WP.theta] at hp
  | div => simp only [run,WP.spec,WP.theta] at hp
  | ok out =>
    simp only [run,WP.spec,WP.theta,WP.wp_return] at hp
    exact ⟨out,rfl,hp⟩

#print axioms loop
end PCF_AppendLoop
