import NJB_ActiveReference
import NJB_DecodeInjective
import RPv_JGa_ActiveLoop
import RPv_FJk_ActiveValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_ActiveAssociation
open Aeneas Aeneas.Std Result FIq_Native.pool_v1.pair_forest_copy_terminal
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
def literalModel (s : Selectors) : R0P.CopySelectors K :=
 { high := fun b=>FIv_NativeArray.value s.high b.val,
   low := fun c=>FIv_NativeArray.value s.low c.val }
theorem index_value {N : Usize} (a : Array NQ N) (n : Nat) (h : n<a.val.length) :
 FIv_NativeArray.value a n=decode (a.val[n]'h) := by
 simp only [FIv_NativeArray.value,List.getElem?_eq_getElem h]
theorem high_same (s : Selectors) (b : Fin 64) :
 decode (NJB_ActiveReference.high s b)=FIv_NativeArray.value s.high b.val := by
 exact (index_value s.high b.val (by rw [s.high.property];have h := b.isLt;scalar_tac)).symm
theorem low_same (s : Selectors) (c : Fin 16) :
 decode (NJB_ActiveReference.low s c)=FIv_NativeArray.value s.low c.val := by
 exact (index_value s.low c.val (by rw [s.low.property];have h := c.isLt;scalar_tac)).symm
theorem model_same (s : Selectors) : NJB_ActiveReference.model s=literalModel s := by
 exact congrArg₂ (fun h l=>({high:=h,low:=l} : R0P.CopySelectors K))
  (funext (high_same s)) (funext (low_same s))
/-- The adopted old literal body is total on exactly the same canonical
selector record. Its own loop/value laws are applied, never hypothesized. -/
theorem cohort (s : Selectors) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) :
 ∃ out,Selectors.active s=ok out ∧ Canon out ∧ decode out=R0P.copyActiveLiteral (literalModel s) := by
 obtain ⟨out,call,ho⟩ := JGa_ActiveLoop.source 64 0#usize s FIq_Native.field.QM31.ZERO rfl hh hl FIv_NativeValue.zero.1
 have value := FJk_ActiveValue.loop 64 0#usize s FIq_Native.field.QM31.ZERO out rfl hh hl FIv_NativeValue.zero.1 call
 refine ⟨out,?_,ho,?_⟩
 · simpa only [Selectors.active,Selectors.active_literal] using call
 · have v := value.2
   change decode out=FJk_ActiveValue.model s 0 (decode FIq_Native.field.QM31.ZERO) at v
   rw [FIv_NativeValue.zero.2] at v
   have step_same : FJk_ActiveValue.step s = fun (sum : K) (block : Fin 64)=>
    if R0P.copyActiveRowMasks block≠0 then sum+FIv_NativeArray.value s.high block.val*
     R0P.copySelectorMaskSum16 (fun c=>FIv_NativeArray.value s.low c.val) (R0P.copyActiveRowMasks block) else sum := by
    funext sum block
    unfold FJk_ActiveValue.step
    rfl
   have model_same : FJk_ActiveValue.model s 0 0=R0P.copyActiveLiteral (literalModel s) := by
    simp only [FJk_ActiveValue.model,FJk_ActiveValue.indices,List.drop_zero]
    rw [step_same]
    rfl
   exact v.trans model_same
/-- Full-Result association, including exact canonical raw words. No successful
child, independent selector, endpoint equality or field-operation premise. -/
theorem result (s : Selectors) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) :
 NJB_ActiveReference.reference s=Selectors.active s := by
 obtain ⟨a,ra,ca,va⟩ := NJB_ActiveReference.result s hh hl
 obtain ⟨b,rb,cb,vb⟩ := cohort s hh hl
 have sameValue : decode a=decode b := by rw [va,model_same];exact vb.symm
 have same := NJB_DecodeInjective.qm a b ca cb sameValue
 rw [ra,rb,same]
#print result
#print axioms index_value
#print axioms high_same
#print axioms low_same
#print axioms model_same
#print axioms cohort
#print axioms result
end AspisR1.NJB_ActiveAssociation
end
