import FJe_Sum3WrapperBridge
import FJe_PreparedInjective
import AspisR1.PoseidonPreparedSum3ActualValue
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3Value
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (prepared)
open ExtractedMaskPreparedState (PreparedFor)
def at {A : Type} (a : Array A 3#usize) (i : Fin 3) : A :=
  a.val[i.val]'(by simpa only [a.property] using i.isLt)
/-- Complete native sum3 VALUE:the prepared witnesses are the SAME ordered
weights,not newly selected existential operands. -/
theorem value (a : Left) (b w : Right) (out : NQ)
    (cw : FIw_ArrayValue.canonical w) (cb : FIw_ArrayValue.canonical b)
    (hp : ∀i : Fin 3,PreparedFor (prepared (at a i)) (qm (at w i)))
    (run : FIq_Native.field.qm31_sum_products3_prepared a b=ok out) :
    Canon out ∧ decode out=
      decode (at w ⟨0,by decide⟩)*decode (at b ⟨0,by decide⟩)+
      decode (at w ⟨1,by decide⟩)*decode (at b ⟨1,by decide⟩)+
      decode (at w ⟨2,by decide⟩)*decode (at b ⟨2,by decide⟩) := by
  have cmem (i : Fin 3) : Canon (at w i) := cw _ (List.getElem_mem _)
  have bmem (i : Fin 3) : Canon (at b i) := cb _ (List.getElem_mem _)
  obtain ⟨v,x0,x1,x2,rv,cv,p0,p1,p2,vv⟩ :=
    PoseidonPreparedSum3ActualValue.actual_sum3_value (left a) (right b)
      (by
        intro i
        refine ⟨qm (at w i),cmem i,?_⟩
        change PreparedFor (prepared (at a i)) (qm (at w i))
        exact hp i)
      (by
        intro i
        change Canon (at b i)
        exact bmem i)
  have same := FJe_Sum3WrapperBridge.same a b
  rw [run,FIv_Map.map_ok,rv] at same
  have e := Result.ok.inj same
  subst v
  have e0 := FJe_PreparedInjective.prepared _ _ _ p0 (hp ⟨0,by decide⟩)
  have e1 := FJe_PreparedInjective.prepared _ _ _ p1 (hp ⟨1,by decide⟩)
  have e2 := FJe_PreparedInjective.prepared _ _ _ p2 (hp ⟨2,by decide⟩)
  subst x0;subst x1;subst x2
  exact ⟨cv,vv⟩
#print axioms value
end AspisR1.FJe_Sum3Value
end
