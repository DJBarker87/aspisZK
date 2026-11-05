import NHI_WordEncoding
set_option autoImplicit false
namespace NHX_KWordLift
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem cell (a b : NQ)
 (words : ∀ i:Nat,i<4→(NHI_WordEncoding.words a).val[i]?=(NHI_WordEncoding.words b).val[i]?) : a=b := by
 apply NHI_WordEncoding.injective
 apply Subtype.ext
 apply List.ext_getElem
 · rw [(NHI_WordEncoding.words a).property,(NHI_WordEncoding.words b).property]
 · intro i hi hj
   have small:i<4:=by rw [(NHI_WordEncoding.words a).property] at hi;exact hi
   have h:=words i small
   exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using h)

theorem vector (a b : Slice NQ) (la:a.val.length=64) (lb:b.val.length=64)
 (words : ∀ i (ha:i<a.val.length) (hb:i<b.val.length),∀ j:Nat,j<4→
  (NHI_WordEncoding.words (a.val[i]'ha)).val[j]?=(NHI_WordEncoding.words (b.val[i]'hb)).val[j]?) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem
 · omega
 · intro i hi hj
   exact cell _ _ (words i hi hj)

#print axioms cell
#print axioms vector
end NHX_KWordLift
