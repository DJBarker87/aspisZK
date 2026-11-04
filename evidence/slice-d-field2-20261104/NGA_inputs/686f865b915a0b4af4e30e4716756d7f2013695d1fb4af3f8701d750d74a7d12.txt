import NGA_Cache
import NFT_ChannelFour
set_option autoImplicit false
namespace NGA_Cell
open Aeneas Aeneas.Std Result
abbrev Cache := NGA_Cache.Cache
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev Cell := Fin 3 × Fin 3
abbrev uFin := AspisR1PoseidonPreparedIndexProductBounds.uFin

def at3 {α : Type} (a : Array α 3#usize) (i : Fin 3) : α :=
 a.val[i.val]'(by simpa [a.property] using i.isLt)
def get {α : Type} (a : Array (Array α 3#usize) 3#usize) (c : Cell) : α := at3 (at3 a c.1) c.2

def set (s : Sums) (c : Cell) (v : U64) : Sums :=
 s.set (uFin c.1) ((at3 s c.1).set (uFin c.2) v)

theorem get_set (s : Sums) (c d : Cell) (v : U64) :
 get (set s c v) d = if d=c then v else get s d := by
 rcases c with ⟨i,j⟩;rcases d with ⟨k,l⟩
 simp only [get,set,at3,Array.set,AspisR1PoseidonPreparedIndexProductBounds.uFin_val]
 by_cases hki : k=i
 · subst k
   by_cases hlj : l=j
   · subst l;simp
   · have hn : l.val≠j.val := by intro h;exact hlj (Fin.ext h)
     simp [List.getElem_set,hn,hlj]
 · have hn : k.val≠i.val := by intro h;exact hki (Fin.ext h)
   simp [List.getElem_set,hn,hki]

/-- Handwritten cut of the original source cell, not an emitted whole helper. -/
def step (s : Sums) (left right : Cache) (component channel : Usize) : Result Sums := do
 let lr ← Array.index_usize left component
 let a ← Array.index_usize lr channel
 let rr ← Array.index_usize right component
 let b ← Array.index_usize rr channel
 let p ← UScalar.mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)
 let row ← Array.index_usize s component
 let old ← Array.index_usize row channel
 let updated ← UScalar.add old p
 let (row,back) ← Array.index_mut_usize s component
 let row ← Array.update row channel updated
 ok (back row)

theorem index (α : Type) (a : Array α 3#usize) (i : Fin 3) :
 Array.index_usize a (uFin i)=ok (at3 a i) := by
 obtain ⟨x,h,hv⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok a (uFin i) (by
   rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val];exact i.isLt)
 simpa only [at3,AspisR1PoseidonPreparedIndexProductBounds.uFin_val,hv] using h

#print axioms get_set
#print axioms index
end NGA_Cell
