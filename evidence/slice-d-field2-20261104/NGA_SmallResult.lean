import NGA_PreparePairs
set_option autoImplicit false
namespace NGA_SmallResult
open Aeneas Aeneas.Std Result
open NGA_PreparePairs
abbrev convert := AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums

def sourceModel (xs : List Input) : Result Q := do
 let sums ← run xs NGA_Small.zero
 convert sums

theorem source (xs : List Input) (arity : xs.length≤4)
 (canonical : ∀ x∈xs, Canonical x.1 ∧ Canonical x.2) :
 ∃ cs sums out,
   prepare xs=ok cs ∧ List.Forall₂ PairFor xs cs ∧ cs.length=xs.length ∧
   run xs NGA_Small.zero=ok sums ∧
   (∀ d, (NGA_Cell.get sums d).val=NGA_Small.terms cs d) ∧
   convert sums=ok out ∧ Canonical out ∧ sourceModel xs=ok out := by
 obtain ⟨cs,hcs,assoc,length,domain⟩ := NGA_PreparePairs.source xs canonical
 obtain ⟨sums,hs,values,_⟩ := NGA_Small.source cs (by rw [length];exact arity) domain
 obtain ⟨out,ho,hcanon⟩ := NFT_Karatsuba.total sums
 have hrun : run xs NGA_Small.zero=ok sums := (same_run xs cs assoc _).trans hs
 exact ⟨cs,sums,out,hcs,assoc,length,hrun,values,ho,hcanon,by simp only [sourceModel,hrun,ho,bind_tc_ok]⟩

#print axioms source
end NGA_SmallResult
