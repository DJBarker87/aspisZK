import RPu_FIx_SquareValue
import RPu_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ValueBitModel
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)

def bit (a : Array NQ 16#usize) (index : Nat) : K :=
  FIv_NativeArray.value a index*FIv_NativeArray.value a index-FIv_NativeArray.value a index

def step (a : Array NQ 16#usize) (offset index : Nat) (old : Fin (33#usize).val → K) :
    Fin (33#usize).val → K := fun j=>if j.val=offset+index then bit a index else old j

def model (a : Array NQ 16#usize) (offset : Nat) : Nat → Nat →
    (Fin (33#usize).val → K) → (Fin (33#usize).val → K)
  | 0,_,old => old
  | n+1,index,old => model a offset n (index+1) (step a offset index old)
end AspisR1.FIx_ValueBitModel
end
