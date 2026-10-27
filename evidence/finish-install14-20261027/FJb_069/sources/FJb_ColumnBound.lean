import FJb_TailRow
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ColumnBound
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FJb_ColumnTable (Table callback)
/-- Derive the final external row's complete table bounds from the SAME
actual native constructor on the SAME stage state. -/
theorem value (s : State) (out : Table)
    (run : array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      callback (Array.repeat 4#usize 0#u64) s=ok out) : FJb_TailCell.Bounded out := by
  intro c i
  let cu : Usize := Usize.ofNatCore c.val (lt_trans c.isLt (4#usize).hBounds)
  let iu : Usize := Usize.ofNatCore i.val (lt_trans i.isLt (4#usize).hBounds)
  have vc : cu.val=c.val := by simp [cu]
  have vi : iu.val=i.val := by simp [iu]
  have hc : cu.val < (4#usize).val := by rw [vc];exact c.isLt
  have hi : iu.val < (4#usize).val := by rw [vi];exact i.isLt
  have hv := (FJb_ColumnTable.value s out run cu hc iu hi).2
  change (FJb_TailCell.cell (FJb_TailCell.cell out ⟨cu.val,hc⟩) ⟨iu.val,hi⟩).val < 2^34 at hv
  have fc : (⟨cu.val,hc⟩ : Fin (4#usize).val)=c := Fin.ext vc
  have fi : (⟨iu.val,hi⟩ : Fin (4#usize).val)=i := Fin.ext vi
  rw [fc,fi] at hv
  exact hv
#print axioms value
end AspisR1.FJb_ColumnBound
end
