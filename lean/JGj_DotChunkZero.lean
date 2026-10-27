import JGj_DotChunkTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_DotChunkZero
open Aeneas Aeneas.Std Result FIq_Native
open JGj_DotChunkSource (Range Raw4)
theorem source (fuel : Nat) (iter : Range) (weights : Slice field.QM31) (values : Slice U32)
    (hwEnd : iter.end.val≤weights.val.length) (hvEnd : iter.end.val≤values.val.length)
    (hspan : iter.start.val+fuel=iter.end.val) (hcount : fuel≤4)
    (hw : JGj_DotChunkTotal.WCanonical weights) (hv : JGj_DotChunkTotal.VCanonical values) :
    ∃ raw,field.qm31_m31_dot_loop1_loop0 iter weights values (Array.repeat 4#usize 0#u64)=ok raw ∧
      JGj_DotInput.Budget raw fuel := by
  have zero : JGj_DotInput.Budget (Array.repeat 4#usize 0#u64) 0 := by
    intro j
    simp only [FJb_TailCell.cell,Array.repeat,List.getElem_replicate,Nat.zero_mul]
    exact Nat.le_refl _
  obtain ⟨raw,ro,bo⟩ := JGj_DotChunkTotal.source fuel iter weights values _ 0 hwEnd hvEnd hspan (by simpa using hcount) hw hv zero
  exact ⟨raw,ro,by simpa only [Nat.zero_add] using bo⟩
#print axioms source
end AspisR1.JGj_DotChunkZero
end
