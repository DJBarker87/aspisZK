import RPu_FJb_WordAt
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_ColumnWords
open Aeneas Aeneas.Std Result FIq_Native
open FJb_MatrixGroupStep (State)
open FJb_ColumnTable (Table callback)
open FJb_TailCell (cell)
open FJb_WordAt (q)
def words (s : State) (c r j : Fin (4#usize).val) : Nat :=
  (cell (FJb_LimbMap.words (q s c r)) j).val
/-- ALL words of one ORIGINAL constructed column come from the SAME four
native cells of the SAME stage state. -/
theorem value (s : State) (sums : Table)
    (run : array_from_fn_copy 4#usize (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      callback (Array.repeat 4#usize 0#u64) s=ok sums) (c : Fin (4#usize).val) :
    (fun j : Fin (4#usize).val=>(cell (cell sums c) j).val)=
      (fun j=>words s c ⟨0,by decide⟩ j+words s c ⟨1,by decide⟩ j+words s c ⟨2,by decide⟩ j+words s c ⟨3,by decide⟩ j) := by
  funext j
  let cu : Usize := Usize.ofNatCore c.val (lt_trans c.isLt (4#usize).hBounds)
  let iu : Usize := Usize.ofNatCore j.val (lt_trans j.isLt (4#usize).hBounds)
  have vc : cu.val=c.val := by simp [cu]
  have vi : iu.val=j.val := by simp [iu]
  have hc : cu.val < (4#usize).val := by rw [vc];exact c.isLt
  have hi : iu.val < (4#usize).val := by rw [vi];exact j.isLt
  have hv := (FJb_ColumnTable.value s sums run cu hc iu hi).1
  change (cell (cell sums ⟨cu.val,hc⟩) ⟨iu.val,hi⟩).val=_ at hv
  have fc : (⟨cu.val,hc⟩ : Fin (4#usize).val)=c := Fin.ext vc
  have fi : (⟨iu.val,hi⟩ : Fin (4#usize).val)=j := Fin.ext vi
  rw [fc,fi] at hv
  have b0 : cu.val < (16#usize).val := by change cu.val < 16;have : cu.val < 4 := hc;omega
  have b1 : 4+cu.val < (16#usize).val := by change 4+cu.val < 16;have : cu.val < 4 := hc;omega
  have b2 : 8+cu.val < (16#usize).val := by change 8+cu.val < 16;have : cu.val < 4 := hc;omega
  have b3 : 12+cu.val < (16#usize).val := by change 12+cu.val < 16;have : cu.val < 4 := hc;omega
  have h0 := FJb_WordAt.group s c ⟨0,by decide⟩ cu.val b0 (by simp [vc]) iu hi j vi
  have h1 := FJb_WordAt.group s c ⟨1,by decide⟩ (4+cu.val) b1 (by simp [vc]) iu hi j vi
  have h2 := FJb_WordAt.group s c ⟨2,by decide⟩ (8+cu.val) b2 (by simp [vc]) iu hi j vi
  have h3 := FJb_WordAt.group s c ⟨3,by decide⟩ (12+cu.val) b3 (by simp [vc]) iu hi j vi
  rw [h0,h1,h2,h3] at hv
  exact hv
#print axioms value
end AspisR1.FJb_ColumnWords
end
