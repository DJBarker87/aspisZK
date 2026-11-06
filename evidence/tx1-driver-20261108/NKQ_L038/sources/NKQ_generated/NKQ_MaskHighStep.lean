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
 let j:=Usize.ofNatCore (16+i.val) (by scalar_tac)
 have bounded : 16+i.val<2^UScalarTy.Usize.numBits := by scalar_tac
 have add : 16#usize+i=ok j := by
  simp [UScalar.add,UScalar.tryMk,UScalar.tryMkOpt,Result.ofOption,j,bounded]
 simp only [FinishModel.closureFn5,FinishModel.closureFn2]
 rw [add,bind_tc_ok]
 simpa only [highAt] using
  NKQ_ReadTwo.readTwo c 0#usize j (by decide) (by change 16+i.val<29;omega)

#print axioms step
end AspisR1.NKQ_MaskHighStep
