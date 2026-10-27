import RPu_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_ArrayReadValue
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

theorem value {N : Usize} (a : Array NQ N) (i : Usize) (hi : i.val<N.val) :
    FIv_NativeArray.value a i.val=FIw_ArrayValue.decoded a ⟨i.val,hi⟩ := by
  unfold FIv_NativeArray.value FIw_ArrayValue.decoded FIw_ArrayValue.cells
  rw [List.getElem?_eq_getElem (by simpa only [a.property] using hi)]

theorem read {N : Usize} (a : Array NQ N) (i : Usize) (hi : i.val<N.val) (out : NQ)
    (run : Array.index_usize a i=ok out) :
    decode out=FIw_ArrayValue.decoded a ⟨i.val,hi⟩ := by
  rw [← value a i hi,FIv_NativeArray.read a i out run]
#print axioms value
#print axioms read
end AspisR1.FIw_ArrayReadValue
end
