import RPu_FJk_CopyFullFold
import RPu_FIw_CopyEvaluation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_CopyRowTransport
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)
theorem cell {N : Usize} (a : Array NQ N) (i : Fin N.val) :
    FIv_NativeArray.value a i.val=decoded a i := by
  simp only [FIv_NativeArray.value,List.getElem?_eq_getElem (by rw [a.property];exact i.isLt)]
  rfl
/-- Same four actual endpoint arrays; no second row witness. -/
theorem value (pv pw cv cw : Array field.QM31 2#usize) :
    FIw_CopyTransport.row ⟨pv,pw,cv,cw⟩=FJk_CopyStep.row pv pw cv cw := by
  have p : (fun i : Fin 2=>FIv_NativeArray.value pv i.val)=decoded pv := funext (cell pv)
  have w : (fun i : Fin 2=>FIv_NativeArray.value pw i.val)=decoded pw := funext (cell pw)
  have c : (fun i : Fin 2=>FIv_NativeArray.value cv i.val)=decoded cv := funext (cell cv)
  have d : (fun i : Fin 2=>FIv_NativeArray.value cw i.val)=decoded cw := funext (cell cw)
  unfold FIw_CopyTransport.row FJk_CopyStep.row
  rw [p,w,c,d]
#print axioms cell
#print axioms value
end AspisR1.FJk_CopyRowTransport
end
