import NGA_ArrayExt
set_option autoImplicit false
namespace NGA_OuterStep
open Aeneas Aeneas.Std Result WP NGA_Cell
abbrev Qm := NGA_Cache.Q

def G {n : Usize} (left right : Array Qm n) (s : Sums) (index : Usize)
 (child : Sums → Qm → Qm → Result Sums) : Result (Sums × Usize) := do
 let l ← Array.index_usize left index
 let r ← Array.index_usize right index
 let next ← child s l r
 let index ← UScalar.add index 1#usize
 ok (next,index)

theorem source {n : Usize} (left right : Array Qm n) (s : Sums) (index : Usize)
 (arity : n.val≤4) (active : index.val<n.val)
 (hl : ∀ x∈left.val, NGA_Cache.Canonical x) (hr : ∀ x∈right.val, NGA_Cache.Canonical x)
 (budget : ∀ d, (get s d).val≤3*(2147483647-1)^2) :
 ∃ l r out next,
   Array.index_usize left index=ok l ∧ Array.index_usize right index=ok r ∧
   NGA_Cache.Canonical l ∧ NGA_Cache.Canonical r ∧
   NGA_Accumulate.sourceModel s l r=ok out ∧ next.val=index.val+1 ∧
   G left right s index NGA_Accumulate.sourceModel=ok (out,next) := by
 obtain ⟨l,hlrun,hval⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok left index active
 obtain ⟨r,hrrun,rval⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok right index active
 have cl := hl l (by rw [hval];exact List.getElem_mem _)
 have cr := hr r (by rw [rval];exact List.getElem_mem _)
 obtain ⟨lc,rc,out,_,_,_,_,ho,_,_⟩ := NGA_Accumulate.source s l r cl cr budget
 have indexbound : index.val<4 := lt_of_lt_of_le active arity
 obtain ⟨next,hn,hvalue,_⟩ := WP.spec_imp_exists (@UScalar.add_spec .Usize index 1#usize (by scalar_tac))
 refine ⟨l,r,out,next,hlrun,hrrun,cl,cr,ho,?_,?_⟩
 · simpa only [UScalar.ofNatCore_val_eq] using hvalue
 · simp only [G,hlrun,hrrun,ho,hn,bind_tc_ok]

#print axioms source
end NGA_OuterStep
