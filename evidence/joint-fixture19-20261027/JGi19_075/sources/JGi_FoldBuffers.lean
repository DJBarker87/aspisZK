import JGg_ViewOpening
set_option autoImplicit false
namespace AspisR1.JGi_FoldBuffers
open Aeneas Aeneas.Std Result

theorem extend (v : alloc.vec.Vec U8) (s : Slice U8) (fits : v.length+s.length≤Usize.max) :
    ∃ out,alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s=ok out ∧ out.val=v.val++s.val := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos fits]
  simp [Slice.clone,core.clone.CloneU8]
#print axioms extend
theorem source (root : Array U8 32#usize) (round1 : Slice U8) (length : round1.length=224) :
    ∃ bytes1 bytes2 : alloc.vec.Vec U8,
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 round1=ok bytes2 ∧
      (alloc.vec.Vec.deref bytes2).val=root.val++round1.val := by
  obtain ⟨b1,first,h1⟩ := extend (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)
    (by simp [alloc.vec.Vec.length,alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,Slice.length,Array.to_slice,root.property];scalar_tac)
  have len1 : b1.length=32 := by
    change b1.val.length=32
    rw [h1]
    simp [alloc.vec.Vec.with_capacity,alloc.vec.Vec.new,Array.to_slice,root.property]
  obtain ⟨b2,second,h2⟩ := extend b1 round1 (by rw [len1,length];scalar_tac)
  refine ⟨b1,b2,first,second,?_⟩
  change b2.val=root.val++round1.val
  rw [h2,h1]
  rfl
#print axioms source
end AspisR1.JGi_FoldBuffers
