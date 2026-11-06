import NKF_Windows
import NKF_PdaModel
set_option autoImplicit false
noncomputable section
namespace NKF_SeedWindows
open Aeneas Aeneas.Std Result
/-- Exact zero-padded byte observation used by NKF_pda.rs, not an address law. -/
def byte (s : List U8) (i : Nat) : U8 := s[i]?.getD 0#u8

theorem bytes (a b : List U8) (lengths : a.length=b.length) (width : a.length≤32)
 (windows : ∀ i : Nat, i<32 → byte a i=byte b i) : a=b := by
 apply List.ext_getElem
 · exact lengths
 · intro i ha hb
   have same := windows i (by omega)
   simpa only [byte,List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.getD_some] using same

structure SeedCut (a b : List (List U8)) : Prop where
 count : a.length=b.length
 capacity : a.length≤5
 widths : ∀ (s : Nat) (h : s<a.length), (a[s]'h).length≤32
 lengths : ∀ s : Nat, s<5 → (a[s]?.getD []).length=(b[s]?.getD []).length
 windows : ∀ s i : Nat, s<5 → i<32 → byte (a[s]?.getD []) i=byte (b[s]?.getD []) i

theorem seeds (a b : List (List U8)) (cut : SeedCut a b) : a=b := by
 apply List.ext_getElem
 · exact cut.count
 · intro s ha hb
   have small : s<5 := by have:=cut.capacity;omega
   have lengths:=cut.lengths s small
   have windows:=cut.windows s
   apply bytes
   · simpa only [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.getD_some] using lengths
   · exact cut.widths s ha
   · intro i hi
     simpa only [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.getD_some] using windows i small hi

/-- Native seed/program images determine the same quantified operation input.
This is only per-call composition, not full registry authentication. -/
theorem invocation {Output : Type} (op : List (List U8) → Array U8 32#usize → Output)
 (a b : List (List U8)) (p q : Array U8 32#usize)
 (cut : SeedCut a b) (program : NKF_Windows.Bounded p q) : op a p=op b q := by
 rw [seeds a b cut,NKF_ArrayFrame.array_ext p q (NKF_Windows.bounded_cells p q program)]

set_option pp.proofs false in
#print seeds
#print axioms bytes
#print axioms seeds
#print axioms invocation
end NKF_SeedWindows
