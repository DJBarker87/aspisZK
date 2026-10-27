import RPu_FJe_Sum3WrapperBridge
import RPu_FJe_PreparedInjective
import RPu_AspisR1.PoseidonPreparedSum3ActualValue
import RPu_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3Value
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (K Canon decode)
open FIv_PreparedNew (prepared)
open ExtractedMaskPreparedState (PreparedFor)
def cell {A : Type} (a : Array A 3#usize) (i : Fin 3) : A :=
  a.val[i.val]'(by rw [a.property];change i.val<3;exact i.isLt)
open AspisR1PoseidonPreparedIndexProductBounds (uFin uFin_val)
theorem mappedCell {A B : Type} (f : A → B) (a : Array A 3#usize) (i : Fin 3) :
    (FJb_ArrayTransport.array f a).val[(uFin i).val]'(by
      rw [uFin_val,(FJb_ArrayTransport.array f a).property]
      change i.val<3
      exact i.isLt)=f (cell a i) := by
  simp only [FJb_ArrayTransport.array,List.getElem_map,uFin_val,cell]
#print axioms mappedCell
/-- Complete native sum3 VALUE:the prepared witnesses are the SAME ordered
weights,not newly selected existential operands. -/
theorem value (a : Left) (b w : Right) (out : NQ)
    (cw : FIw_ArrayValue.canonical w) (cb : FIw_ArrayValue.canonical b)
    (hp : ∀i : Fin 3,PreparedFor (prepared (cell a i)) (qm (cell w i)))
    (run : FIq_Native.field.qm31_sum_products3_prepared a b=ok out) :
    Canon out ∧ decode out=
      decode (cell w ⟨0,by decide⟩)*decode (cell b ⟨0,by decide⟩)+
      decode (cell w ⟨1,by decide⟩)*decode (cell b ⟨1,by decide⟩)+
      decode (cell w ⟨2,by decide⟩)*decode (cell b ⟨2,by decide⟩) := by
  have cmem (i : Fin 3) : Canon (cell w i) := cw _ (List.getElem_mem _)
  have bmem (i : Fin 3) : Canon (cell b i) := cb _ (List.getElem_mem _)
  obtain ⟨v,x0,x1,x2,rv,cv,p0,p1,p2,vv⟩ :=
    PoseidonPreparedSum3ActualValue.actual_sum3_value (left a) (right b)
      (by
        intro i
        refine ⟨qm (cell w i),cmem i,?_⟩
        change PreparedFor ((left a).val[(uFin i).val]'_) (qm (cell w i))
        exact Eq.mpr (congrArg (fun p=>PreparedFor p (qm (cell w i)))
          (mappedCell prepared a i)) (hp i))
      (by
        intro i
        change ExtractedMaskQM31Exact.CurrentCanonicalQM ((right b).val[(uFin i).val]'_)
        exact Eq.mpr (congrArg ExtractedMaskQM31Exact.CurrentCanonicalQM
          (mappedCell qm b i)) (bmem i))
  have same := FJe_Sum3WrapperBridge.same a b
  rw [run,FIv_Map.map_ok,rv] at same
  have e := Result.ok.inj same
  subst v
  change PreparedFor ((left a).val[(uFin ⟨0,by decide⟩).val]'_) x0 at p0
  change PreparedFor ((left a).val[(uFin ⟨1,by decide⟩).val]'_) x1 at p1
  change PreparedFor ((left a).val[(uFin ⟨2,by decide⟩).val]'_) x2 at p2
  have p0' := Eq.mp (congrArg (fun p=>PreparedFor p x0) (mappedCell prepared a ⟨0,by decide⟩)) p0
  have p1' := Eq.mp (congrArg (fun p=>PreparedFor p x1) (mappedCell prepared a ⟨1,by decide⟩)) p1
  have p2' := Eq.mp (congrArg (fun p=>PreparedFor p x2) (mappedCell prepared a ⟨2,by decide⟩)) p2
  have e0 := FJe_PreparedInjective.prepared _ _ _ p0' (hp ⟨0,by decide⟩)
  have e1 := FJe_PreparedInjective.prepared _ _ _ p1' (hp ⟨1,by decide⟩)
  have e2 := FJe_PreparedInjective.prepared _ _ _ p2' (hp ⟨2,by decide⟩)
  subst x0;subst x1;subst x2
  change decode out=
    decode (cell w ⟨0,by decide⟩)*ExtractedMaskQM31Exact.decode ((right b).val[(uFin ⟨0,by decide⟩).val]'_)+
    decode (cell w ⟨1,by decide⟩)*ExtractedMaskQM31Exact.decode ((right b).val[(uFin ⟨1,by decide⟩).val]'_)+
    decode (cell w ⟨2,by decide⟩)*ExtractedMaskQM31Exact.decode ((right b).val[(uFin ⟨2,by decide⟩).val]'_) at vv
  unfold right at vv
  have term (i : Fin 3) := congrArg
    (fun x=>decode (cell w i)*ExtractedMaskQM31Exact.decode x) (mappedCell qm b i)
  exact ⟨cv,vv.trans (congrArg₂ (fun x y : K=>x+y)
    (congrArg₂ (fun x y : K=>x+y) (term ⟨0,by decide⟩) (term ⟨1,by decide⟩))
    (term ⟨2,by decide⟩))⟩
#print axioms value
end AspisR1.FJe_Sum3Value
end
