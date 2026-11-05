import NHI_FactoredProducers
import NHI_Scalar
set_option autoImplicit false
namespace NHM_FactoredTerm
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def term (powers : Array NE 4#usize) (factors : Array NQ 4#usize) (s : Usize) : Result NE := do
 let index ← Array.index_usize FIo_Native.weights.PERM s
 let x ← Array.index_usize powers index
 let q ← Array.index_usize factors s
 let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x q
 FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product FIo_Native.weights.QUARTER

/-- Every term uses the SAME permuted producer entry and SAME factor entry. -/
theorem total (powers : Array NE 4#usize) (factors : Array NQ 4#usize)
 (hp : ∀ x∈powers.val,canonE x) (hf : ∀ x∈factors.val,canonQ x)
 (s : Usize) (small : s.val<4) : ∃ out,term powers factors s=ok out ∧ canonE out := by
 obtain ⟨index,hi,ib⟩:=NHI_ScalarDomain.perm s small
 let x:=NHI_ScalarDomain.pick powers index.val ib
 let q:=NHI_ScalarDomain.pick factors s.val small
 have cx:=NHI_ScalarDomain.canon_pick canonE powers hp index.val ib
 have cq:=NHI_ScalarDomain.canon_pick canonQ factors hf s.val small
 obtain ⟨product,hm,cm,_⟩:=NHE_ScalarProductLaw.product x q cx cq
 dsimp only [x,q] at hm
 obtain ⟨out,ho,co,_⟩:=NGM_RoundScale.total product
 refine ⟨out,?_,co⟩
 simp only [term,hi,NHI_ScalarDomain.index powers index ib,
  NHI_ScalarDomain.index factors s small,hm,bind_tc_ok]
 simpa only [FIo_Native.weights.QUARTER] using ho

#print axioms total
end NHM_FactoredTerm
