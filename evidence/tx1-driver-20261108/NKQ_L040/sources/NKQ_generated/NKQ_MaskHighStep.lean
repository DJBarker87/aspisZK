import NKQ_ReadTwo
set_option autoImplicit false
namespace AspisR1.NKQ_MaskHighStep
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NKQ_ArrayWindows
abbrev Q := aspis_core.field.QM31
abbrev Claims := Array (Array Q 29#usize) 3#usize

def highAt (c : Claims) (i : Usize) (h : i.val<10) : Q :=
 cell (cell c 0 (by decide)) (16+i.val) (by change 16+i.val<29;omega)

theorem step {H : Type} (D : aspis_core.Digest32 H) (c : Claims)
 (i : Usize) (inside : i.val<10) :
 (FinishModel.closureFn5 D).call_mut c i=ok (highAt c i inside,c) := by
 have zero : (0#usize).val=0 := by scalar_tac
 have sixteen : (16#usize).val=16 := by scalar_tac
 obtain ⟨j,add,jval⟩:=WP.spec_imp_exists (UScalar.add_spec (x:=16#usize) (y:=i) (by scalar_tac))
 have value : j.val=16+i.val := by simpa only [sixteen] using jval
 simp only [FinishModel.closureFn5,FinishModel.closureFn2]
 rw [add,bind_tc_ok]
 simpa only [highAt,zero,value] using
  NKQ_ReadTwo.readTwo c 0#usize j (by decide) (by rw [value];change 16+i.val<29;omega)

#print axioms step
end AspisR1.NKQ_MaskHighStep
