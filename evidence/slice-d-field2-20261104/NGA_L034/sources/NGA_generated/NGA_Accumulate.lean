import NGA_CacheValues
set_option autoImplicit false
namespace NGA_Accumulate
open Aeneas Aeneas.Std Result NGA_Cell NGA_Converter
abbrev Qm := NGA_Cache.Q

def sourceModel (s : Sums) (left right : Qm) : Result Sums := do
 let l ← NGA_Cache.prelude left
 let r ← NGA_Cache.prelude right
 NGA_Nine.run NGA_Nine.trace s l r

theorem source (s : Sums) (left right : Qm)
 (hl : NGA_Cache.Canonical left) (hr : NGA_Cache.Canonical right)
 (budget : ∀ d, (get s d).val≤3*(2147483647-1)^2) :
 ∃ l r out,
   NGA_Cache.prelude left=ok l ∧ NGA_Cache.prelude right=ok r ∧
   NGA_CacheDomain.Bounded l ∧ NGA_CacheDomain.Bounded r ∧
   sourceModel s left right=ok out ∧
   (∀ d, (get out d).val=(get s d).val+NGA_Nine.product l r d) ∧
   interpret (decode out)=interpret (decode s)+NGA_ChannelAlgebra.decodeQ left*NGA_ChannelAlgebra.decodeQ right := by
 obtain ⟨l,hlrun,cl,_⟩ := NGA_CacheDomain.source left hl
 obtain ⟨r,hrrun,cr,_⟩ := NGA_CacheDomain.source right hr
 obtain ⟨out,ho,values⟩ := NGA_Nine.source s l r cl cr budget
 refine ⟨l,r,out,hlrun,hrrun,cl,cr,?_,values,?_⟩
 · simp only [sourceModel,hlrun,hrrun,ho,bind_tc_ok]
 · have state : decode out = fun d => decode s d+
     NGA_ChannelAlgebra.channels left d*NGA_ChannelAlgebra.channels right d := by
     funext d
     simp only [decode,values d,Nat.cast_add,NGA_Nine.product,Nat.cast_mul]
     rw [NGA_CacheValues.source left hl l hlrun d,NGA_CacheValues.source right hr r hrrun d]
   rw [state,NGA_ChannelAlgebra.add,NGA_ChannelAlgebra.product]

#print axioms source
end NGA_Accumulate
