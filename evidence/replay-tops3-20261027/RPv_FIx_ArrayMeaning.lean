import RPv_FIw_ArrayReadValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ArrayMeaning
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded cells)

theorem decoded_of_map {N : Usize} (a : Array NQ N) (f : Fin N.val → K)
    (values : a.val.map decode=List.ofFn f) : decoded a=f := by
  funext i
  have hi : i.val<a.val.length := by simpa only [a.property] using i.isLt
  have he := congrArg (fun xs : List K=>xs[i.val]?) values
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.some.injEq] at he
  exact he

theorem decoded_repeat (N : Usize) (x : NQ) : decoded (Array.repeat N x)=fun _=>decode x := by
  funext i
  simp only [decoded,cells,Array.repeat,List.getElem_replicate]

#print axioms decoded_of_map
#print axioms decoded_repeat
end AspisR1.FIx_ArrayMeaning
end
