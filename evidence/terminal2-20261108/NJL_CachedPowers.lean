import NJL_WindowPowers
import NJL_WindowCache
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_CachedPowers
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIv_PreparedNew (NP)
structure Packet (lambda : NQ) where
 powers : List NQ
 next : NQ
 eight : powers.length=8
 power_call : NJL_WindowPowers.run lambda 8 lambda=ok (powers,next)
 power_trace : NJL_WindowPowers.Trace lambda 8 lambda powers next
 canonical : ∀ x∈powers,Canon x
 values : ∀ i (hi : i<powers.length),decode powers[i]=decode lambda*decode lambda^i
 caches : {xs : List NP // xs.length=powers.length}
 cache_call : NJB_Traverse.run FIq_Native.field.PreparedQm31Multiplier.new powers=ok caches
 domains : List.Forall₂ (fun power cache=>FIq_Native.field.PreparedQm31Multiplier.new power=ok cache ∧
  NJB_PreparedLaws.Domain cache power) powers caches.val
/-- Powers8 and actual ordered Prepared::new map8 are from the SAME emitted
field Results; canonical lambda is the only input domain. Full native mutable
powers-array frame and14tail/cohort composition remain separate obligations. -/
theorem source (lambda : NQ) (hl : Canon lambda) : Nonempty (Packet lambda) := by
 obtain ⟨powers,next,call,trace,length,canonical,_,values,_⟩ := NJL_WindowPowers.source lambda lambda 8 hl hl
 obtain ⟨caches,cacheCall,domains⟩ := NJL_WindowCache.source powers canonical
 exact ⟨⟨powers,next,length,call,trace,canonical,values,caches,cacheCall,domains⟩⟩
#print Packet
#print source
#print axioms source
end AspisR1.NJL_CachedPowers
end
