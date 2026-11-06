import NKQ_ClaimsDomain
import NKQ_AlphaDomain
import NKQ_MaskCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_FinishMaskDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

/-- Source-ordered producer substitution at136: SAME parsed prefix, actual
round carry, actual quantified-reservation claims. No selected claims/alpha,
child success, endpoint equation or operation dictionary is a hypothesis.
This proves caller domains only, not native136 or the OPEN terminal result. -/
theorem source {H : Type} (native : NJM_RoundsCut.Observations) (cut : NJM_RoundsCut.Cut native)
 (token frame : Nat) (reservation : NP6_StdModel.Reservation)
 (D : aspis_core.Digest32 H) (bytes : Slice U8) (t : r1_wire.SemanticTranscript H) :
 match parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes with
 | .ok (.Ok pre) =>
   match rounds : (PreparedHashCode.run (S1SemanticCode.rounds NJM_RoundJoin.R D (PrefixAdapter.fromOld pre) t)).2 with
   | .ok (.Ok after) =>
     match claimed : ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation) (PrefixAdapter.fromOld pre) with
     | .ok (.Ok c) =>
       ∃ (low : Std.Array aspis_core.field.QM31 16#usize) (high : Std.Array aspis_core.field.QM31 10#usize),
        (IDa_Deployed.boundaries reservation).fromFn 16#usize (FinishModel.closureFn9 D) c=ok low ∧
        (IDa_Deployed.boundaries reservation).fromFn 10#usize (FinishModel.closureFn5 D) c=ok high ∧
        (∀ q∈low.val,NKQ_MaskCuts.Canon q) ∧ (∀ q∈high.val,NKQ_MaskCuts.Canon q) ∧
        NKQ_MaskCuts.Canon (NKQ_MaskCuts.blind c) ∧ NKQ_MaskCuts.CanonAlpha after.2.1
     | _ => True
   | _ => True
 | _ => True := by
 split
 · rename_i pre parsed
   split
   · rename_i after returned
     split
     · rename_i c claimed
       have alpha:=NKQ_AlphaDomain.source native cut token frame D bytes t
       rw [parsed,returned] at alpha
       have claims:=NKQ_ClaimsDomain.source reservation bytes
       rw [parsed,claimed] at claims
       change NKQ_MaskCuts.CanonClaims c at claims
       have fields:=NKQ_MaskCanonical.domain c after.2.1 claims alpha
       exact ⟨_,_,NKQ_MaskArrays.low_source reservation D c,NKQ_MaskArrays.high_source reservation D c,
        fields.1,fields.2.1,fields.2.2.1,fields.2.2.2⟩
     all_goals trivial
   all_goals trivial
 · trivial
#print axioms source
#print source
end AspisR1.NKQ_FinishMaskDomain
end
