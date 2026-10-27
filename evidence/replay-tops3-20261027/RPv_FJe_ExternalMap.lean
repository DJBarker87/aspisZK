import RPv_FJe_ExternalCalls
import RPv_FIy_MapValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ExternalMap
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
open FJe_ExternalCalls (Packed callback)
/-- All four actual final output calls;the captured sum is the SAME value
through the map,and every addition's value is derived from its actual call. -/
theorem value (p out : Packed) (total : NQ) (hp : canonical p) (ht : Canon total)
    (run : FIq_Native.core.array.Array.map callback p total=ok out) :
    canonical out ∧ decoded out=fun j=>decoded p j+decode total := by
  unfold FIq_Native.core.array.Array.map at run
  have v := FIy_MapValue.value callback Canon decode (fun x=>decode x+decode total)
    p total out (by
      intro x hx y last call
      change (do let q ← field.QM31.add x total;ok (q,total))=ok (y,last) at call
      obtain ⟨q,rq,tail⟩ := FIv_Map.bind_success _ _ _ call
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj tail)
      have one := FIv_NativeValue.add x total q (hp x hx) ht rq
      exact ⟨one.1,one.2,rfl⟩) run
  refine ⟨v.1,?_⟩
  funext j
  have ve := congrArg (fun xs=>xs[j.val]?) v.2
  rw [List.getElem?_map,List.getElem?_map,
    List.getElem?_eq_getElem (by simpa only [out.property] using j.isLt),
    List.getElem?_eq_getElem (by simpa only [p.property] using j.isLt)] at ve
  exact Option.some.inj ve
#print axioms value
end AspisR1.FJe_ExternalMap
end
