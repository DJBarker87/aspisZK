import Port5Q1_ListCells
set_option autoImplicit false
namespace AspisR1.Port5Q1_MapPoint

theorem transfer {A B C : Type} (f : A → C) (g : B → C)
    (xs : List A) (ys : List B) (a : A) (b : B)
    (meaning : xs.map f=ys.map g) (i : Nat) (hi : i<ys.length) :
    f (xs[i]?.getD a)=g (ys[i]?.getD b) := by
  have lengths := congrArg List.length meaning
  simp only [List.length_map] at lengths
  have hx : i<xs.length := by omega
  have eq := congrArg (fun zs : List C => zs[i]?) meaning
  rw [List.getElem?_map,List.getElem?_map,
    List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hi] at eq
  have result := Option.some.inj eq
  rw [List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hi]
  exact result

#print axioms transfer
end AspisR1.Port5Q1_MapPoint
