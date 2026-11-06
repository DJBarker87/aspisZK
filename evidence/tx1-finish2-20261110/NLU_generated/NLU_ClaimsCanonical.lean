import NLU_CanonicalTransport
import NKQ_ClaimsDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
/-- The SAME parsed claims call produces the complete256 claims domain.
Reservation Err and all aborts remain separate arms, never premises. -/
theorem claims_domain (r : NP6_StdModel.Reservation) (bytes : Slice U8)
 (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre)) :
 match ClaimsUnrolledFinish.claims (NP6_StdModel.calls r) (PrefixAdapter.fromOld pre) with
 | .ok (.Ok c)=>∀ row∈(mapArray (mapArray toQ) c).val,FIw_ArrayValue.canonical row
 | _=>True := by
 have canonical:=NKQ_ClaimsDomain.source r bytes
 rw [parsed] at canonical
 dsimp only at canonical
 cases h : ClaimsUnrolledFinish.claims (NP6_StdModel.calls r) (PrefixAdapter.fromOld pre) with
 | fail err=>trivial
 | div=>trivial
 | ok out=>
   cases out with
   | Err err=>trivial
   | Ok c=>
     unfold NKQ_ClaimsDomain.Outcome at canonical
     rw [h] at canonical
     exact claims_to_native c canonical
#print axioms claims_domain
end AspisR1.NLU_Terminal
end
