import NGH_AccumulateRef
import NGA_SumAlgebra
set_option autoImplicit false
namespace NGH_SmallRef
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Input := NGA_PreparePairs.Input
abbrev Q := NGA_Cache.Q

def loop : List Input → Sums → Result Sums
 | [], sums => ok sums
 | pair::rest, sums => do
   let next ← NGH_AccumulateRef.run sums pair.1 pair.2
   loop rest next

def run (pairs : List Input) : Result Q := do
 let sums ← loop pairs NGA_Small.zero
 NGA_SmallResult.convert sums

theorem loop_eq (pairs : List Input) (sums : Sums) :
 loop pairs sums=NGA_PreparePairs.run pairs sums := by
 induction pairs generalizing sums with
 | nil => rfl
 | cons p ps ih =>
   simp only [loop,NGH_AccumulateRef.model_eq,NGA_PreparePairs.run,NGA_Accumulate.sourceModel,bind_assoc_eq]
   congr 1
   funext l
   congr 1
   funext r
   congr 1
   funext next
   exact ih next

theorem model_eq (pairs : List Input) : run pairs=NGA_SmallResult.sourceModel pairs := by
 simp only [run,loop_eq,NGA_SmallResult.sourceModel]

#print axioms loop_eq
#print axioms model_eq
end NGH_SmallRef
