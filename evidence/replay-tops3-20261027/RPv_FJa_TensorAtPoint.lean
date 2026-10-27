import RPv_FJa_WeightBits
import RPv_FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_TensorAtPoint
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)
/-- Convert an ofFn point tensor to the retained literal selector, using the
existing MSB-first bitWeight/selAt theorem. -/
theorem ofFn (alpha : Fin 10 → K) (r : Fin 1024) :
    FJa_TensorMeaning.weight (List.ofFn alpha) r.val=R0P.SemSource.selAt alpha r := by
  have v := FJa_WeightBits.value (List.ofFn alpha) r.val
  change FJa_TensorMeaning.weight (List.ofFn alpha) r.val=R0P.SemDegree.bitWeight 10
    (fun i => (List.ofFn alpha)[i.val]'(by rw [List.length_ofFn];exact i.isLt)) r.val at v
  simp only [List.getElem_ofFn] at v
  rw [v,R0P.SemDegree.selAt_eq_bitWeight]
/-- The literal point list consists of exactly its original decoded cells. -/
theorem list (point : Array NQ 10#usize) :
    point.val.map decode=List.ofFn (FIw_ArrayValue.decoded point) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<10
  · have hb : i<point.val.length := by rw [point.property];exact hi
    rw [List.getElem?_map,List.getElem?_eq_getElem hb]
    simp only [List.getElem?_ofFn,show (10#usize).val=10 from rfl,hi,↓reduceDIte,Option.map_some]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_map,point.property];exact Nat.le_of_not_gt hi),
      List.getElem?_eq_none (by rw [List.length_ofFn];exact Nat.le_of_not_gt hi)]
#print axioms ofFn
#print axioms list
end AspisR1.FJa_TensorAtPoint
end
