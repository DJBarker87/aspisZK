import LPm_PublicState
set_option autoImplicit false
namespace NDL_DotCarrier
open Aeneas Aeneas.Std
abbrev Dot := FIo_Native.fast_pairing.EbyKDot

def word (x : Dot) (i : Nat) : U64 :=
  if i<4 then x.c0.sums.val[i]! else x.c1.sums.val[i-4]!

/-- Native high-dot's eight raw words AND count determine the SAME full
emitted mutable accumulator. No validity or arithmetic relation is assumed. -/
theorem injective (x y : Dot) (count : x.count=y.count)
    (same : ∀ i,i<8 → word x i=word y i) : x=y := by
  rcases x with ⟨⟨a⟩,⟨b⟩,c⟩
  rcases y with ⟨⟨d⟩,⟨e⟩,f⟩
  have ad : a.val=d.val := by
    apply List.ext_getElem
    · rw [a.property,d.property]
    · intro i hi hj
      have small : i<4 := by simpa only [a.property,show (4#usize).val=4 from rfl] using hi
      have h := same i (by omega)
      simpa [word,small,List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using h
  have be : b.val=e.val := by
    apply List.ext_getElem
    · rw [b.property,e.property]
    · intro i hi hj
      have small : i<4 := by simpa only [b.property,show (4#usize).val=4 from rfl] using hi
      have h := same (i+4) (by omega)
      have large : ¬i+4<4 := by omega
      simpa [word,large,List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using h
  have ha : a=d := Subtype.ext ad
  have hb : b=e := Subtype.ext be
  change c=f at count
  cases ha;cases hb;cases count;rfl

#print axioms injective
end NDL_DotCarrier
