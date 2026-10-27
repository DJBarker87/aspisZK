import FJq_MainCells
import FIw_BuilderValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_MainIndices
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (decode)
theorem value {N : Usize} (out : Array MQ N) (f : Nat → FIv_NativeValue.K)
    (h : out.val.map decode=(OraclePortStdBuilder.indices N).map (fun i=>f i.val)) :
    ∀ i : Fin N.val,decode (FJq_MainCells.cell out i)=f i.val := by
  have mapped : out.val.map decode=List.ofFn (fun i : Fin N.val=>f i.val) := by
    simpa only [OraclePortStdBuilder.indices,List.map_ofFn,Function.comp_def] using h
  intro i
  have hi : i.val<out.val.length := by rw [out.property];exact i.isLt
  have got:=congrArg (fun xs : List FIv_NativeValue.K=>xs[i.val]?) mapped
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    List.getElem?_ofFn,i.isLt,dif_pos,Option.some.injEq,FJq_MainCells.cell] using got
#print axioms value
end AspisR1.FJq_MainIndices
end
