import PCI_DepositWords
import PCI_ListWindow
import NFY_Part005
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_DepositWordWindow

def cut (h : Array U8 80#usize) (base : Nat) (bound : base+32≤80) : Array U8 32#usize :=
 ⟨h.val.slice base (base+32),by
   change (h.val.slice base (base+32)).length=32
   have hh : h.val.length=80 := h.property
   simp only [List.slice,List.length_take,List.length_drop]
   omega⟩

theorem word (h : Array U8 80#usize) (base i : Nat) (bound : base+32≤80) (index : i<8) :
    NFY_NBG_WideBytes.word (cut h base bound) i=PCI_DepositRead.model_word h (base+4*i) := by
 have hh : h.val.length=80 := h.property
 have g0 := PCI_ListWindow.get h.val base 32 (4*i) (by omega) (by omega)
 have g1 := PCI_ListWindow.get h.val base 32 (4*i+1) (by omega) (by omega)
 have g2 := PCI_ListWindow.get h.val base 32 (4*i+2) (by omega) (by omega)
 have g3 := PCI_ListWindow.get h.val base 32 (4*i+3) (by omega) (by omega)
 unfold NFY_NBG_WideBytes.word PCI_DepositRead.model_word cut
 simp only [g0,g1,g2,g3,Nat.add_assoc]

theorem limbs (h : Array U8 80#usize) (base : Nat) (bound : base+32≤80) :
    NFY_NBG_WideBytes.limbs (cut h base bound)=PCI_DepositWords.model h base := by
 unfold NFY_NBG_WideBytes.limbs PCI_DepositWords.model
 rw [word h base 0 bound (by omega),word h base 1 bound (by omega),word h base 2 bound (by omega),word h base 3 bound (by omega),word h base 4 bound (by omega),word h base 5 bound (by omega),word h base 6 bound (by omega),word h base 7 bound (by omega)]

#print axioms word
#print axioms limbs
end PCI_DepositWordWindow
