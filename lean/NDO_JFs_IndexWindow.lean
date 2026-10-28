import NDO_JFt_Index
set_option autoImplicit false
namespace AspisR1.JFs_IndexWindow
open Aeneas Aeneas.Std Result

theorem source (off n small : Nat) (bound : off+n≤1880)
    (i : Usize) (inside : i.val<n) (insideSmall : i.val<small)
    (byte : U8) (xs : List U8)
    (selected : (JFx_NativeBytes.publicInput.val.drop off).take small=xs)
    (value : xs[i.val]?=some byte) :
    Slice.index_usize (JFu_PublicRange.segment off n bound) i=ok byte := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.length];exact inside) byte
  dsimp only [JFu_PublicRange.segment]
  rw [List.getElem?_take_of_lt inside]
  have h:=congrArg (fun ys : List U8 => ys[i.val]?) selected
  rw [List.getElem?_take_of_lt insideSmall] at h
  exact h.trans value

#print axioms source
end AspisR1.JFs_IndexWindow
