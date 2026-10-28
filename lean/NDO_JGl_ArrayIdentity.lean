import NDO_JGb_DecodeInjective
import RPv_FIw_ArrayValue
set_option autoImplicit false
namespace AspisR1.JGl_ArrayIdentity
open Aeneas Aeneas.Std FIq_Native
open FIw_ArrayValue (canonical decoded cells)
theorem value {N : Usize} (a b : Array field.QM31 N)
    (ha : canonical a) (hb : canonical b) (same : decoded a=decoded b) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro n hn hm
    let i : Fin N.val := ⟨n,by simpa only [a.property] using hn⟩
    exact JGb_DecodeInjective.source (cells a i) (cells b i)
      (ha _ (List.getElem_mem _)) (hb _ (List.getElem_mem _)) (congrFun same i)
#print axioms value
end AspisR1.JGl_ArrayIdentity
