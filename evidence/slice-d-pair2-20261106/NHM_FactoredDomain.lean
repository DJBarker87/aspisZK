import NHM_FactoredPrefix
import NHM_FactoredTerm
set_option autoImplicit false
namespace NHM_FactoredDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem producers (extra : Array NQ 2#usize) (hc : ∀ q∈extra.val,canonQ q)
 (side : Usize) (hs : side.val<2) :
 ∃ q low high q4 q16,Array.index_usize extra side=ok q ∧
 NHI_FactoredProducers.run q=ok (low,high,q4,q16) ∧
 (∀ x∈low.val,canonQ x) ∧ (∀ x∈high.val,canonQ x) ∧ canonQ q4 ∧ canonQ q16 := by
 let q:=NHI_ScalarDomain.pick extra side.val hs
 have cq:=NHI_ScalarDomain.canon_pick canonQ extra hc side.val hs
 obtain ⟨low,high,q4,q16,run,cl,ch,c4,c16⟩:=NHI_FactoredProducers.total q cq
 exact ⟨q,low,high,q4,q16,NHI_ScalarDomain.index extra side hs,run,cl,ch,c4,c16⟩

/-- Exact scalar-factor domain from the SAME producer tuple and SAME ap0. -/
theorem low_scalar (powers : Array NE 4#usize) (hp : ∀ x∈powers.val,canonE x)
 (q : NQ) (hq : canonQ q) :
 ∃ low high q4 q16 scalar,
 NHI_FactoredProducers.run q=ok (low,high,q4,q16) ∧
 FIo_Native.weights.Weights.scalar_factor low powers=ok scalar ∧ canonE scalar ∧
 (∀ x∈high.val,canonQ x) ∧ canonQ q4 ∧ canonQ q16 := by
 obtain ⟨low,high,q4,q16,run,cl,ch,c4,c16⟩:=NHI_FactoredProducers.total q hq
 obtain ⟨sum,scalar,fold,cs,hs,co,values⟩:=NHI_Scalar.total low powers hp cl
 exact ⟨low,high,q4,q16,scalar,run,hs,co,ch,c4,c16⟩

#print axioms producers
#print axioms low_scalar
end NHM_FactoredDomain
