import FIw_OpeningValues
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIw_OpeningPointwise
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

theorem value (a : Array NQ 16#usize) (model : Usize → K)
    (values : a.val.map decode=(OraclePortStdBuilder.indices 16#usize).map model)
    (j : Fin 16) :
    FIw_ArrayValue.decoded a j=model (UScalar.ofNatCore j.val (by scalar_tac)) := by
  have slot := congrArg (fun xs : List K=>xs[j.val]?) values
  have bound : a.val.length=16 := a.property
  have hj : j.val<a.val.length := by rw [bound];exact j.isLt
  simp [OraclePortStdBuilder.indices,List.getElem?_eq_getElem hj,j.isLt] at slot
  simpa only [FIw_ArrayValue.decoded,FIw_ArrayValue.cells] using slot
#print axioms value
end AspisR1.FIw_OpeningPointwise
end
