import Aeneas
set_option autoImplicit false
namespace AspisR1.NBA_ArrayEight
open Aeneas Aeneas.Std Result

theorem read {α : Type} (a : Array α 8#usize) (i : Usize) (hi : i.val<8) :
    Array.index_usize a i=ok (a.val[i.val]'(by have := a.property; change a.val.length=8 at this; omega)) := by
  obtain ⟨v,call,value⟩ := WP.spec_imp_exists
    (Array.index_usize_spec a i (by simpa only [Array.length,a.property,show (8#usize).val=8 by rfl] using hi))
  rw [value] at call
  exact call

theorem literal {α : Type} (a : Array α 8#usize) :
    a.val=[a.val[0]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[1]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[2]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[3]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[4]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[5]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[6]'(by have := a.property; change a.val.length=8 at this; omega),
      a.val[7]'(by have := a.property; change a.val.length=8 at this; omega)] := by
  apply List.ext_getElem
  · simpa only [List.length_cons,List.length_nil] using a.property
  · intro i hi hj
    have bound : i<8 := by have := a.property; change a.val.length=8 at this; omega
    interval_cases i <;> rfl

#print axioms read
#print axioms literal
end AspisR1.NBA_ArrayEight
