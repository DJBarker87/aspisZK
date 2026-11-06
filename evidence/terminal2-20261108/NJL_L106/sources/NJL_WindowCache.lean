import NJL_Traverse
import NJB_PreparedCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowCache
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
/-- K045/K046 actual std array::map binding, including all NINE words of
every callback result, is paired with this ordered complete Result list.
The callback is ACTUAL PreparedQm31Multiplier.new; no cache-validity input. -/
theorem source (powers : List NQ) (canonical : ∀ x∈powers,Canon x) :
 ∃ caches,NJB_Traverse.run FIq_Native.field.PreparedQm31Multiplier.new powers=ok caches ∧
 List.Forall₂ (fun power cache=>FIq_Native.field.PreparedQm31Multiplier.new power=ok cache ∧
  NJB_PreparedLaws.Domain cache power) powers caches.val := by
 obtain ⟨caches,call,_,relation⟩ := NJL_Traverse.packet FIq_Native.field.PreparedQm31Multiplier.new
  (fun _=>True) (fun power cache=>FIq_Native.field.PreparedQm31Multiplier.new power=ok cache ∧ NJB_PreparedLaws.Domain cache power)
  powers (by
   intro power hp
   obtain ⟨cache,call,domain⟩ := NJB_PreparedLaws.new_result power (canonical power hp)
   exact ⟨cache,call,True.intro,call,domain⟩)
 exact ⟨caches,call,relation⟩
#print source
#print axioms source
end AspisR1.NJL_WindowCache
end
