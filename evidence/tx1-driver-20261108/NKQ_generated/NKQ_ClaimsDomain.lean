import NKQ_ClaimsMatrix
import NKA_ClaimsEffects
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_ClaimsDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation ClaimsUnrolledFinish

/-- Exact field-preserving parent/main carrier conversion, after three SAME
successful decodes; no buffer identity is inferred from an address. -/
theorem convert (value : AspisR1ClaimsUnrolledParent.Claims)
 (canonical : NKQ_ClaimsMatrix.ParentCanon value) :
 NKQ_MaskCuts.CanonClaims (NKA_ClaimsEffects.main value) := by
 intro row rowMember
 change row∈value.val.map toMainArray at rowMember
 obtain ⟨parentRow,parentMember,sameRow⟩:=List.mem_map.mp rowMember
 subst row
 intro q valueMember
 change q∈parentRow.val.map toMainQM at valueMember
 obtain ⟨original,originalMember,sameValue⟩:=List.mem_map.mp valueMember
 subst q
 exact canonical parentRow parentMember original originalMember

def Outcome (result : Result (core.result.Result MainClaims MainError)) : Prop :=
 match result with
 | .ok (.Ok value) => NKQ_MaskCuts.CanonClaims value
 | _ => True

/-- Actual parser branch, quantified Reservation and fixed deployed claims
implementation. Every successful caller value is canonical; allocation Err,
parse rejection and outer abort stay separate branches. No source-success or
chosen claims value is an external premise. -/
theorem source (reservation : NP6_StdModel.Reservation) (bytes : Slice U8) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) => Outcome (claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre))
 | _ => True := by
 split
 · rename_i pre parsed
   obtain ⟨value,pure,parent⟩:=NKA_ClaimsModel.parsed reservation bytes pre parsed
   have canonical:=convert value (NKQ_ClaimsMatrix.reference _ value pure)
   have mapped : claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre)=
    toMainStatus (NKA_ClaimsModel.reserveResult reservation value) := by
     exact congrArg toMainStatus parent
   rw [mapped]
   cases reservation with
   | Err error => trivial
   | Ok unit => cases unit;exact canonical
 · trivial
#print axioms convert
#print axioms source
#print source
end AspisR1.NKQ_ClaimsDomain
end
