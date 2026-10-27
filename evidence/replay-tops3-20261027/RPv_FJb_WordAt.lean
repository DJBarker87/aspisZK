import RPv_FJb_TailStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_WordAt
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FJb_MatrixGroupStep (State)
open FJb_TailCell (cell)
def q (s : State) (c r : Fin (4#usize).val) : NQ :=
  FIw_ArrayValue.cells s ⟨4*r.val+c.val,by
    have hc : c.val < 4 := c.isLt
    have hr : r.val < 4 := r.isLt
    change 4*r.val+c.val < 16
    omega⟩

theorem value (s : State) (n : Nat) (hn : n < (16#usize).val)
    (limb : Usize) (hi : limb.val < (4#usize).val) (j : Fin (4#usize).val)
    (hj : limb.val=j.val) :
    FJb_ColumnCell.atWord s n limb hi=
      cell (FJb_LimbMap.words (FIw_ArrayValue.cells s ⟨n,hn⟩)) j := by
  unfold FJb_ColumnCell.atWord
  rw [dif_pos hn]
  change cell (FJb_LimbMap.words (FIw_ArrayValue.cells s ⟨n,hn⟩)) ⟨limb.val,hi⟩=_
  exact congrArg (cell (FJb_LimbMap.words (FIw_ArrayValue.cells s ⟨n,hn⟩))) (Fin.ext hj)

theorem group (s : State) (c r : Fin (4#usize).val) (n : Nat)
    (hn : n < (16#usize).val) (hindex : n=4*r.val+c.val)
    (limb : Usize) (hi : limb.val < (4#usize).val) (j : Fin (4#usize).val)
    (hj : limb.val=j.val) :
    (FJb_ColumnCell.atWord s n limb hi).val=(cell (FJb_LimbMap.words (q s c r)) j).val := by
  rw [value s n hn limb hi j hj]
  have fs : (⟨n,hn⟩ : Fin (16#usize).val)=⟨4*r.val+c.val,by
    have hc : c.val < 4 := c.isLt
    have hr : r.val < 4 := r.isLt
    change 4*r.val+c.val < 16
    omega⟩ := Fin.ext hindex
  exact congrArg (fun k : Fin (16#usize).val=>
    (cell (FJb_LimbMap.words (FIw_ArrayValue.cells s k)) j).val) fs
#print axioms value
#print axioms group
end AspisR1.FJb_WordAt
end
