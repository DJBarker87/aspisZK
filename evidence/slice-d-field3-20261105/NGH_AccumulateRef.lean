import NGA_ArrayExt
set_option autoImplicit false
namespace NGH_AccumulateRef
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Q := NGA_Cache.Q
-- The cache and checked scalar step are reused by exact names, not copied.
def cells : List Cell → Sums → Cache → Cache → Result Sums
 | [], sums, _, _ => ok sums
 | cell::rest, sums, left, right => do
   let next ← NGA_Cell.step sums left right (uFin cell.1) (uFin cell.2)
   cells rest next left right

def run (sums : Sums) (left right : Q) : Result Sums := do
 let l ← NGA_Cache.prelude left
 let r ← NGA_Cache.prelude right
 cells NGA_Nine.trace sums l r

theorem cells_eq (trace : List Cell) (sums : Sums) (left right : Cache) :
 cells trace sums left right=NGA_Nine.run trace sums left right := by
 induction trace generalizing sums with
 | nil => rfl
 | cons c cs ih => simp only [cells,NGA_Nine.run];congr 1;funext next;exact ih next

theorem model_eq (sums : Sums) (left right : Q) :
 run sums left right=NGA_Accumulate.sourceModel sums left right := by
 simp only [run,NGA_Accumulate.sourceModel,cells_eq]

theorem cohort (sums : Sums) (left right : Q)
 (hl : NGA_Cache.Canonical left) (hr : NGA_Cache.Canonical right)
 (budget : ∀ d, (get sums d).val≤3*(2147483647-1)^2) :
 ∃ out, run sums left right=ok out ∧
 NGA_Converter.interpret (NGA_Converter.decode out)=
 NGA_Converter.interpret (NGA_Converter.decode sums)+
 NGA_ChannelAlgebra.decodeQ left*NGA_ChannelAlgebra.decodeQ right := by
 obtain ⟨l,r,out,_,_,_,_,ho,_,hv⟩ := NGA_Accumulate.source sums left right hl hr budget
 exact ⟨out,(model_eq sums left right).trans ho,hv⟩
#print axioms cells_eq
#print axioms model_eq
#print axioms cohort
end NGH_AccumulateRef
