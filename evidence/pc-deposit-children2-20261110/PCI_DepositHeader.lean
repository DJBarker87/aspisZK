import PCI_ListWindow
import PCI_DepositActual.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositHeader

def header80 (bytes : Slice U8) (extent : 80≤bytes.length) : Array U8 80#usize :=
 ⟨bytes.val.take 80,by
  change (bytes.val.take 80).length=80
  have h : 80≤bytes.val.length := extent
  simp only [List.length_take]
  omega⟩

theorem get (bytes : Slice U8) (extent : 80≤bytes.length) (i : Nat) (index : i<80) :
    (header80 bytes extent).val[i]! = bytes.val[i]! := by
 have h : 80≤bytes.val.length := extent
 have left : i<(bytes.val.take 80).length := by simp only [List.length_take];omega
 have right : i<bytes.val.length := by omega
 have hl := List.getElem!_of_getElem? (List.getElem?_eq_getElem left)
 have hr := List.getElem!_of_getElem? (List.getElem?_eq_getElem right)
 change (bytes.val.take 80)[i]! = bytes.val[i]!
 rw [hl,hr]
 simp only [List.getElem_take]

#print axioms get
end PCI_DepositHeader
