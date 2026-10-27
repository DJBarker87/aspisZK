import FJa_SplitStep
import FJa_SplitModel
import FIw_WordValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SplitValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIv_PreparedNew (NP)
open FIw_ArrayValue (canonical)
/-- Exact two-write value on the SAME array and the SAME native arithmetic
operands returned by a successful split step. -/
theorem writes {N : Usize} (weights middle afterWrite : Array NQ N)
    (p : NP) (c parent right left : NQ) (index i i1 : Usize)
    (hc : Canon c) (hw : canonical weights)
    (hp : field.PreparedQm31Multiplier.new c=ok p)
    (hparent : Array.index_usize weights index=ok parent)
    (hright : field.PreparedQm31Multiplier.mul p parent=ok right)
    (hleft : field.QM31.sub parent right=ok left)
    (hi : 2#usize*index=ok i) (hm : Array.update weights i left=ok middle)
    (hi1 : i+1#usize=ok i1) (ha : Array.update middle i1 right=ok afterWrite) :
    FIv_NativeArray.value afterWrite = FJa_SplitModel.step (decode c) (FIv_NativeArray.value weights) index.val := by
  have v := FIz_SelectorSplit.value c parent right left p hc
    (FIv_NativeArray.canonical weights index parent hw hparent) hp hright hleft
  have pv := FIv_NativeArray.read weights index parent hparent
  have iv : i.val=2*index.val := FIw_WordValue.mul _ _ _ hi
  have i1v : i1.val=i.val+1 := FIw_WordValue.add _ _ _ hi1
  funext j
  rw [FJa_ArrayUpdate.value middle afterWrite i1 right ha j,
    FJa_ArrayUpdate.value weights middle i left hm j]
  unfold FJa_SplitModel.step
  simp only [Function.update_apply,iv,i1v,v.2.2.1,v.2.2.2.1,←pv]
  split <;> split <;> simp_all only [eq_comm]
#print axioms writes
end AspisR1.FJa_SplitValue
end
