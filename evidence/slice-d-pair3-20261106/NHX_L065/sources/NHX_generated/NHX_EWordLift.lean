import NHM_EEncoding
set_option autoImplicit false
namespace NHX_EWordLift
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem cell (a b:NE) (words:∀ i:Nat,i<8→
 (NGM_RawWords.nativeWords a).val[i]?=(NGM_RawWords.nativeWords b).val[i]?) : a=b:=by
 have same:NGM_RawWords.nativeWords a=NGM_RawWords.nativeWords b:=by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [(NGM_RawWords.nativeWords a).property,(NGM_RawWords.nativeWords b).property]
  · intro i hi hj
    have small:i<8:=by rw [(NGM_RawWords.nativeWords a).property] at hi;exact hi
    have h:=words i small
    exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using h)
 have eq:=congrArg NHM_EEncoding.record same
 simpa only [NHM_EEncoding.roundtrip] using eq

theorem array {n:Usize} (a b:Array NE n)
 (words:∀ i (ha:i<a.val.length) (hb:i<b.val.length),∀ j:Nat,j<8→
 (NGM_RawWords.nativeWords (a.val[i]'ha)).val[j]?=(NGM_RawWords.nativeWords (b.val[i]'hb)).val[j]?) : a=b:=by
 apply Subtype.ext
 apply List.ext_getElem
 · exact a.property.trans b.property.symm
 · intro i hi hj
   exact cell _ _ (words i hi hj)

#print axioms cell
#print axioms array
end NHX_EWordLift
