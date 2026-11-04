import NFB_TerminalFrame
set_option autoImplicit false
namespace NFB_ResizeAssociation
open Aeneas Aeneas.Std Result NFB_PhysicalFrame NFB_PrivateFrame

theorem complete (count : Usize) :
 ∃ out : alloc.vec.Vec U32,
 alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
  (alloc.vec.Vec.with_capacity U32 count) count 0#u32=ok out ∧
 out.val=List.replicate count.val 0#u32 := by
 obtain ⟨out,run,values⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.resize_spec core.marker.CopyU32.cloneInst
   (alloc.vec.Vec.with_capacity U32 count) count 0#u32 rfl)
 refine ⟨out,run,?_⟩
 simpa only [alloc.vec.Vec.with_capacity,List.resize] using values

theorem payload (count : Nat) (heap : Heap)
 (selected : heap Place.inverse.id=some []) :
 NFB_PhysicalFrame.run (NFB_TerminalFrame.resize count) heap Place.inverse.id=
 some (List.replicate count 0#u32) := by
 have general : ∀ (n : Nat) (before : List U32) (heap : Heap),
    heap Place.inverse.id=some before →
    NFB_PhysicalFrame.run (NFB_TerminalFrame.resize n) heap Place.inverse.id=
    some (before++List.replicate n 0#u32) := by
  intro n
  induction n with
  | zero => intro before heap h;simpa only [NFB_TerminalFrame.resize,NFB_PhysicalFrame.run,List.replicate_zero,List.append_nil] using h
  | succ n ih =>
   intro before heap h
   change NFB_PhysicalFrame.run (NFB_TerminalFrame.resize n)
    ((append .inverse [0#u32]).apply heap) Place.inverse.id=_
   have next : (append .inverse [0#u32]).apply heap Place.inverse.id=some (before++[0#u32]) := by
    simp only [append,Action.apply,write,ite_true,h,Option.map_some]
   have result:=ih (before++[0#u32]) _ next
   simpa only [List.append_assoc,List.replicate_succ,List.singleton_append] using result
 simpa only [List.nil_append] using general count [] heap selected
#print axioms complete
#print axioms payload
end NFB_ResizeAssociation
