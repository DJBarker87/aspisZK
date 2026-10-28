import RPv_FJe_ThreeColumnStep
import RPv_JFy_ArrayTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_ThreeStepTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open FJb_MatrixGroupStep (State)
open FJb_M31Step (Constants Bounded)
open FJe_ThreeColumnStep (Weights)
theorem source (w : Weights) (c0 c1 c2 : Constants) (s : State) (i : Usize)
    (hi : i.val<(16#usize).val) (hw : canonical w)
    (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) (hs : canonical s) :
    ∃ out,FJe_ThreeColumnStep.step w c0 c1 c2 s i=ok out ∧ canonical out := by
  obtain ⟨w0,r0,cw0⟩ := JFy_ArrayTotal.read w 0#usize (by decide) hw
  obtain ⟨w1,r1,cw1⟩ := JFy_ArrayTotal.read w 1#usize (by decide) hw
  obtain ⟨w2,r2,cw2⟩ := JFy_ArrayTotal.read w 2#usize (by decide) hw
  let k0 := FJb_TailCell.cell c0 ⟨i.val,hi⟩
  let k1 := FJb_TailCell.cell c1 ⟨i.val,hi⟩
  let k2 := FJb_TailCell.cell c2 ⟨i.val,hi⟩
  have rk0 : Array.index_usize c0 i=ok k0 := RawPoseidonExternalRowReads.array_index_usize_ok c0 i hi
  have rk1 : Array.index_usize c1 i=ok k1 := RawPoseidonExternalRowReads.array_index_usize_ok c1 i hi
  have rk2 : Array.index_usize c2 i=ok k2 := RawPoseidonExternalRowReads.array_index_usize_ok c2 i hi
  obtain ⟨q,rq,cq,_⟩ := FJe_ThreeCell.source_success w0 w1 w2 k0 k1 k2 cw0 cw1 cw2 (h0 _) (h1 _) (h2 _)
  obtain ⟨out,ro,co⟩ := JFy_ArrayTotal.update s i q hi hs cq
  exact ⟨out,by simp only [FJe_ThreeColumnStep.step,r0,r1,r2,rk0,rk1,rk2,rq,ro,bind_tc_ok],co⟩
#print axioms source
end AspisR1.JGj_ThreeStepTotal
end
