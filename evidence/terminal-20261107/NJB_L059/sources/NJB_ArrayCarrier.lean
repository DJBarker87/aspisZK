import NJB_ArrayReads
set_option autoImplicit false
namespace AspisR1.NJB_ArrayCarrier
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
def cell {α : Type} {N : Usize} (a : Array α N) (i : Fin N.val) : α :=
 a.val[i.val]'(by simpa only [a.property] using i.isLt)
def array {α : Type} {N : Usize} (f : Fin N.val → α) : Array α N :=
 Array.make N (List.ofFn f) (by simp only [List.length_ofFn])
theorem cell_array {α : Type} {N : Usize} (f : Fin N.val → α) : cell (array f)=f := by
 funext i
 simp only [cell,array,Array.make,List.getElem_ofFn]
theorem array_cell {α : Type} {N : Usize} (a : Array α N) : array (cell a)=a := by
 apply Subtype.ext
 apply List.ext_getElem
 · simp only [array,Array.make,List.length_ofFn,a.property]
 · intro i hi hj
   simp only [array,Array.make,List.getElem_ofFn,cell]
theorem canonical_cell {N : Usize} (a : Array NQ N) (canonical : FIw_ArrayValue.canonical a) :
 ∀ i,Canon (cell a i) := fun i=>canonical _ (List.getElem_mem _)
theorem canonical_array {N : Usize} (f : Fin N.val → NQ) (canonical : ∀ i,Canon (f i)) :
 FIw_ArrayValue.canonical (array f) := by
 intro x hx
 obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
 exact canonical i
#print axioms cell_array
#print axioms array_cell
#print axioms canonical_cell
#print axioms canonical_array
end AspisR1.NJB_ArrayCarrier
