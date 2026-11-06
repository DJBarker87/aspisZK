import RPv_FJe_ThreeColumns
import NHU_Interpolation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_ColumnTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJb_MatrixGroupStep (State)
open FJe_ThreeColumnStep (Weights model step)
open FJb_M31Step (Constants Bounded)

/-- All four scalar children are instantiated on these SAME array reads.
No child-success premise: scalar totality supplies each complete Result. -/
theorem step_total (w : Weights) (c0 c1 c2 : Constants) (s : State) (i : Usize)
    (hi : i.val < (16#usize).val) (hw : canonical w)
    (h0 : Bounded c0) (h1 : Bounded c1) (h2 : Bounded c2) :
    ∃ out, step w c0 c1 c2 s i = ok out := by
  let w0 := FJb_TailCell.cell w (⟨0,by decide⟩ : Fin (3#usize).val)
  let w1 := FJb_TailCell.cell w (⟨1,by decide⟩ : Fin (3#usize).val)
  let w2 := FJb_TailCell.cell w (⟨2,by decide⟩ : Fin (3#usize).val)
  let k0 := FJb_TailCell.cell c0 ⟨i.val,hi⟩
  let k1 := FJb_TailCell.cell c1 ⟨i.val,hi⟩
  let k2 := FJb_TailCell.cell c2 ⟨i.val,hi⟩
  have r0 : Array.index_usize w 0#usize = ok w0 := RawPoseidonExternalRowReads.array_index_usize_ok w _ (by decide)
  have r1 : Array.index_usize w 1#usize = ok w1 := RawPoseidonExternalRowReads.array_index_usize_ok w _ (by decide)
  have r2 : Array.index_usize w 2#usize = ok w2 := RawPoseidonExternalRowReads.array_index_usize_ok w _ (by decide)
  have rc0 : Array.index_usize c0 i = ok k0 := RawPoseidonExternalRowReads.array_index_usize_ok c0 i hi
  have rc1 : Array.index_usize c1 i = ok k1 := RawPoseidonExternalRowReads.array_index_usize_ok c1 i hi
  have rc2 : Array.index_usize c2 i = ok k2 := RawPoseidonExternalRowReads.array_index_usize_ok c2 i hi
  obtain ⟨q,rq,_,_⟩ := FJe_ThreeCell.source_success w0 w1 w2 k0 k1 k2
    (FIv_NativeArray.canonical w _ w0 hw r0)
    (FIv_NativeArray.canonical w _ w1 hw r1)
    (FIv_NativeArray.canonical w _ w2 hw r2) (h0 _) (h1 _) (h2 _)
  obtain ⟨out,ru,_⟩ := WP.spec_imp_exists (Array.update_spec s i q (by simpa only [s.property] using hi))
  refine ⟨out,?_⟩
  simp only [step,r0,r1,r2,rc0,rc1,rc2,rq,ru,bind_tc_ok]

#print step_total
#print axioms step_total
end AspisR1.NKG_ColumnTotal
end
