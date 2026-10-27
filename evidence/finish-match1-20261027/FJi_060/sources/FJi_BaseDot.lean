import FJi_HeadValue
import FJi_PackProduct
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_BaseDot
open Aeneas Aeneas.Std
open FJi_Accumulations

def sumTo (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) : Nat → AspisWideTower.WideExact
  | 0 => 0
  | n+1 => sumTo q g slot n+FIp_ArrayValue.value g n*
      FJi_WidePack.base (FJi_Inputs.scalar q slot (FJi_Inputs.cursor n)).val

theorem packed (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (n : Nat) :
    FJi_WidePack.pack (fun j=>(FJi_InnerStep.sum q g slot j.val 0 n : FJi_WidePack.F))=sumTo q g slot n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FJi_InnerStep.sum,Nat.zero_add,Nat.cast_add]
    rw [FJi_WidePack.add,ih,FJi_PackProduct.value,sumTo]

theorem model (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) :
    FJi_HeadValue.model q g slot=sumTo q g slot 26 := packed q g slot 26
#print axioms packed
#print axioms model
end AspisR1.FJi_BaseDot
end
