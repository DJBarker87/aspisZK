import RPv_FJj_TensorOuterStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_TensorOuterLoop
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
open FJj_TensorOuterStep

theorem value (self : FIo_Native.weights.Weights) (k : Usize) (row : Row)
    (hr : Array.index_usize self.factors k=ok row)
    (hc : ∀ digit∈row.val,FJf_QMArray.canon digit) (len : Nat)
    (iter : FIo_RangeNext.Range) (input out : Slice NQ) (n : Usize)
    (inv : Inv self row len (iter,self,input,n))
    (run : FIo_Native.weights.Weights.tensor_loop0 iter self k input n=ok out) :
    Post row len out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State=>FIo_Native.weights.Weights.tensor_loop0.body k t.1 t.2.1 t.2.2.1 t.2.2.2)
    (Inv self row len) (Post row len) measure
    (fun t h r hr'=>by cases r <;> exact step self k row hr hc len t h _ hr')
    (iter,self,input,n) out inv run
#print axioms value
end AspisR1.FJj_TensorOuterLoop
end
