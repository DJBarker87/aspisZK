import Aeneas
set_option autoImplicit false
namespace PCI_ListWindow

theorem get {T : Type} [Inhabited T] (xs : List T) (start n i : Nat)
    (extent : start+n≤xs.length) (index : i<n) :
    (xs.slice start (start+n))[i]! = xs[start+i]! := by
  have left : i<(xs.slice start (start+n)).length := by
    simp only [List.slice,List.length_take,List.length_drop]
    omega
  have right : start+i<xs.length := by omega
  have hl := List.getElem!_of_getElem? (List.getElem?_eq_getElem left)
  have hr := List.getElem!_of_getElem? (List.getElem?_eq_getElem right)
  rw [hl,hr]
  simp only [List.slice,List.getElem_take,List.getElem_drop]

#print axioms get
end PCI_ListWindow
