import FIx_PathStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathAlgebra
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

def step (lane : Nat) (selector bit : NQ) (a a1 : Array NQ 16#usize)
    (old : Fin (17#usize).val → K) : Fin (17#usize).val → K :=
  fun j=>if j.val=9+lane then
    decode selector*decode bit*(FIv_NativeArray.value a1 (8+lane)-FIv_NativeArray.value a (1+lane))
    else if j.val=1+lane then
    decode selector*(1-decode bit)*(FIv_NativeArray.value a1 lane-FIv_NativeArray.value a (1+lane))
    else old j

theorem value (lane : Usize) (hl : lane.val<8) (selector bit : NQ) (a a1 : Array NQ 16#usize)
    (old : Fin (17#usize).val → K) :
    FIx_PathStep.model lane hl selector bit a a1 old=step lane.val selector bit a a1 old := by
  funext j
  simp only [FIx_PathStep.model,step,Function.update_apply,Fin.ext_iff]
#print axioms value
end AspisR1.FIx_PathAlgebra
end
