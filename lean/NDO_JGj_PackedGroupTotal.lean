import NDO_JGj_LocalPackedTotal
import RPv_FJe_PackedGroupStep
import RPv_JFy_Specs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_PackedGroupTotal
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJe_PackedGroupStep (Packed)
theorem indices (s : State) (p : Packed) (g i0 i1 i2 i3 : Usize)
    (hg : g.val<4) (h0 : i0.val<16) (h1 : i1.val<16) (h2 : i2.val<16) (h3 : i3.val<16)
    (hs : canonical s) (hp : canonical p) :
    ∃ out,FJe_PackedGroupStep.atIndices s p g i0 i1 i2 i3=ok out ∧ canonical out := by
  obtain ⟨x0,r0,c0⟩ := JFy_ArrayTotal.read s i0 h0 hs
  obtain ⟨x1,r1,c1⟩ := JFy_ArrayTotal.read s i1 h1 hs
  obtain ⟨x2,r2,c2⟩ := JFy_ArrayTotal.read s i2 h2 hs
  obtain ⟨x3,r3,c3⟩ := JFy_ArrayTotal.read s i3 h3 hs
  have ca : canonical (Array.make 4#usize [x0,x1,x2,x3]) := by
    intro x hx
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption
  obtain ⟨q,rq,cq⟩ := JGj_LocalPackedTotal.source _ ca
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update p g q hg hp cq
  refine ⟨out,?_,co⟩
  simp only [FJe_PackedGroupStep.atIndices,r0,r1,r2,r3,rq,ro,bind_tc_ok]
theorem source (s : State) (p : Packed) (g : Usize) (hg : g.val<4)
    (hs : canonical s) (hp : canonical p) :
    ∃ out,FJe_PackedGroupStep.step s p g=ok out ∧ canonical out := by
  obtain ⟨i0,i1,i2,i3,next,h0,v0,h1,v1,h2,v2,h3,v3,_,_⟩ := FJb_GroupIndices.value g hg
  rw [FJe_PackedGroupStep.factor s p g i0 i1 i2 i3 h0 h1 h2 h3]
  exact indices s p g i0 i1 i2 i3 hg (by omega) (by omega) (by omega) (by omega) hs hp
#print axioms indices
#print axioms source
end AspisR1.JGj_PackedGroupTotal
end
