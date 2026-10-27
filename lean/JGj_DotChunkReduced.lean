import JGj_DotChunkZero
import JGj_DotReduceLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_DotChunkReduced
open Aeneas Aeneas.Std Result FIq_Native
open JGj_DotChunkSource (Range)
open JGj_RawBounds
/-- Forward actual chunk and actual coordinate reduction on that SAME raw
result. This is not the enclosing two-chunk seven-term wrapper. -/
theorem source (fuel : Nat) (iter : Range) (weights : Slice field.QM31) (values : Slice U32)
    (sums : Raw) (n : Nat)
    (hwEnd : iter.end.val≤weights.val.length) (hvEnd : iter.end.val≤values.val.length)
    (hspan : iter.start.val+fuel=iter.end.val) (hcount : fuel≤4)
    (hw : JGj_DotChunkTotal.WCanonical weights) (hv : JGj_DotChunkTotal.VCanonical values)
    (hn : n+4≤10) (hs : Bound sums (n*P)) :
    ∃ raw out,field.qm31_m31_dot_loop1_loop0 iter weights values (Array.repeat 4#usize 0#u64)=ok raw ∧
      JGj_DotInput.Budget raw fuel ∧
      field.qm31_m31_dot_loop1_loop1 ⟨0#usize,4#usize⟩ sums raw=ok out ∧ Bound out ((n+4)*P) := by
  obtain ⟨raw,rr,br⟩ := JGj_DotChunkZero.source fuel iter weights values hwEnd hvEnd hspan hcount hw hv
  obtain ⟨out,ro,bo⟩ := JGj_DotReduceLoop.source 4 ⟨0#usize,4#usize⟩ sums raw n (by decide) rfl hn hs
  exact ⟨raw,out,rr,br,ro,bo⟩
#print axioms source
end AspisR1.JGj_DotChunkReduced
end
