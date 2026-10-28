import R1Z.PV_CBL_GenericArrayFlatten
import R1Z.PV_CBL_PadListFacts
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ArrayShape
open PV_CBL_LibraryShapes
set_option autoImplicit false
inductive Shape where
  | zero
  | even : Shape → Shape
  | odd : Shape → Shape

def size : Shape → Nat
  | .zero => 0
  | .even s => size s+size s
  | .odd s => size s+size s+1

def Carrier (T : Type) : Shape → Type
  | .zero => Array T 0#usize
  | .even s => Even T (Carrier T s)
  | .odd s => Odd T (Carrier T s)

def flatten {T : Type} : (s : Shape) → Carrier T s → List T
  | .zero,v => v.val
  | .even s,v => PV_CBL_GenericArrayFlatten.even (flatten s) v
  | .odd s,v => PV_CBL_GenericArrayFlatten.odd (flatten s) v

def build {T : Type} : (s : Shape) → (Nat → T) → Carrier T s
  | .zero,_ => Array.make 0#usize []
  | .even s,f => ⟨build s f,build s (fun i => f (size s+i)),()⟩
  | .odd s,f => ⟨build s f,build s (fun i => f (size s+i)),f (size s+size s)⟩

theorem length {T : Type} (s : Shape) (v : Carrier T s) : (flatten s v).length=size s := by
  induction s with
  | zero => exact v.property
  | even s ih => simp only [flatten,PV_CBL_GenericArrayFlatten.even,List.length_append,ih,size]
  | odd s ih => simp only [flatten,PV_CBL_GenericArrayFlatten.odd,List.length_append,List.length_singleton,ih,size]

theorem flatten_build {T : Type} (s : Shape) (f : Nat → T) :
    flatten s (build s f)=List.ofFn (fun i : Fin (size s) => f i.val) := by
  induction s generalizing f with
  | zero => rfl
  | even s ih =>
    change flatten s (build s f)++flatten s (build s (fun i => f (size s+i)))=_
    rw [ih,ih]
    simp only [size,List.ofFn_add]
    rfl
  | odd s ih =>
    change flatten s (build s f)++flatten s (build s (fun i => f (size s+i)))++[f (size s+size s)]=_
    rw [ih,ih]
    simp only [size,List.ofFn_succ_last,List.ofFn_add,List.append_assoc]
    rfl

theorem reconstruct {T : Type} [Inhabited T] (s : Shape) (xs : List T) (h : xs.length=size s) :
    flatten s (build s (fun i => xs[i]!))=xs := by
  rw [flatten_build]
  apply List.ext_getElem?
  intro i
  by_cases hi : i<size s
  · have hx : i<xs.length := by omega
    rw [List.getElem?_ofFn]
    simp only [dif_pos hi]
    rw [List.getElem?_eq_getElem hx,PV_CBL_PadListFacts.get_bang xs i hx]
  · rw [List.getElem?_ofFn]
    simp only [dif_neg hi]
    exact (List.getElem?_eq_none_iff.mpr (by omega)).symm

def out28 : Shape := .even (.even (.odd (.odd (.odd .zero))))
def out32 : Shape := .even (.even (.even (.even (.even (.odd .zero)))))
theorem size28 : size out28=28 := rfl
theorem size32 : size out32=32 := rfl

#print axioms Shape
#print axioms size
#print axioms Carrier
#print axioms flatten
#print axioms build
#print axioms length
#print axioms flatten_build
#print axioms reconstruct
#print axioms out28
#print axioms out32
#print axioms size28
#print axioms size32
end R1Z.PV_DL_ArrayShape
