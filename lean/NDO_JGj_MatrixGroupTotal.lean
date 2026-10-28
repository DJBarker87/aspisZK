import NDO_JGj_ExternalRowTotal
import NDO_JGj_LimbMapTotal
import RPv_FJb_MatrixBlock
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_MatrixGroupTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
theorem indices (s : State) (i0 i1 i2 i3 : Usize)
    (h0 : i0.val<16) (h1 : i1.val<16) (h2 : i2.val<16) (h3 : i3.val<16)
    (hs : canonical s) :
    ∃ out,FJb_MatrixGroupStep.step s i0 i1 i2 i3=ok out ∧ canonical out := by
  obtain ⟨x0,r0,c0⟩ := JFy_ArrayTotal.read s i0 h0 hs
  obtain ⟨x1,r1,c1⟩ := JFy_ArrayTotal.read s i1 h1 hs
  obtain ⟨x2,r2,c2⟩ := JFy_ArrayTotal.read s i2 h2 hs
  obtain ⟨x3,r3,c3⟩ := JFy_ArrayTotal.read s i3 h3 hs
  obtain ⟨raw,rr⟩ := JGj_LimbMapTotal.source (Array.make 4#usize [x0,x1,x2,x3])
  obtain ⟨y0,ry0,cy0⟩ := JGj_ExternalRowTotal.source raw 0#usize (by decide)
  obtain ⟨y1,ry1,cy1⟩ := JGj_ExternalRowTotal.source raw 1#usize (by decide)
  obtain ⟨y2,ry2,cy2⟩ := JGj_ExternalRowTotal.source raw 2#usize (by decide)
  obtain ⟨y3,ry3,cy3⟩ := JGj_ExternalRowTotal.source raw 3#usize (by decide)
  obtain ⟨s0,rs0,cs0⟩ := JFy_ArrayTotal.update s i0 y0 h0 hs cy0
  obtain ⟨s1,rs1,cs1⟩ := JFy_ArrayTotal.update s0 i1 y1 h1 cs0 cy1
  obtain ⟨s2,rs2,cs2⟩ := JFy_ArrayTotal.update s1 i2 y2 h2 cs1 cy2
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update s2 i3 y3 h3 cs2 cy3
  refine ⟨out,?_,co⟩
  simp only [FJb_MatrixGroupStep.step,r0,r1,r2,r3,rr,ry0,ry1,ry2,ry3,rs0,rs1,rs2,ro,bind_tc_ok]
theorem source (s : State) (g : Usize) (hg : g.val<4)
    (hs : canonical s) :
    ∃ out,FJb_MatrixBlock.block s g=ok out ∧ canonical out := by
  obtain ⟨i0,i1,i2,i3,next,h0,v0,h1,v1,h2,v2,h3,v3,_,_⟩ := FJb_GroupIndices.value g hg
  rw [FJb_MatrixBlock.factor s g i0 i1 i2 i3 h0 h1 h2 h3]
  exact indices s i0 i1 i2 i3 (by omega) (by omega) (by omega) (by omega) hs
#print axioms indices
#print axioms source
end AspisR1.JGj_MatrixGroupTotal
end
